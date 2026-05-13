#!/usr/bin/env bash
# Build SoPlex's bundled CMake project and extract its object files for
# relinking into `libleansoplex.a` by the Lake build.
#
# Idempotent: subsequent runs are cheap (CMake reuses its cache; ar
# re-extraction overwrites in place). Safe to invoke unconditionally
# from CI and from local dev loops.
#
# Outputs:
#   build-soplex/lib/libsoplex.a          — SoPlex static library
#   .lake/build/soplex-objs/*.o           — extracted object files
#   .lake/build/soplex-objs/.ready        — marker file picked up by Lake
#
# Run with the repo root as cwd.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SRC_DIR="$ROOT/soplex"
BUILD_DIR="$ROOT/build-soplex"
OBJS_DIR="$ROOT/.lake/build/soplex-objs"

if [ ! -f "$SRC_DIR/CMakeLists.txt" ]; then
  echo "ERROR: SoPlex submodule not initialised at $SRC_DIR" >&2
  echo "       Run: git submodule update --init --recursive" >&2
  exit 1
fi

# On Linux, compile SoPlex with clang++ -stdlib=libc++ so its object
# files use the same C++ runtime as the bridge and Lake's link-time
# libc++abi.a. macOS and Windows use their native default C++ compiler.
if [ "$(uname -s)" = "Linux" ]; then
  : "${CC:=clang}"
  : "${CXX:=clang++}"
  : "${CXXFLAGS:=-stdlib=libc++}"
  export CC CXX CXXFLAGS
fi

# Opt-in ASan/UBSan instrumentation of SoPlex's own .o files. The CI job
# `linux-asan` exports LEAN_SOPLEX_SANITIZE=1 and pairs this with
# `lake build -Ksanitize=1` so the bridge .o and final exe link see
# matching -fsanitize=... flags.
WANT_SAN=0
if [ -n "${LEAN_SOPLEX_SANITIZE:-}" ] && [ "${LEAN_SOPLEX_SANITIZE}" != "0" ]; then
  WANT_SAN=1
  CXXFLAGS="${CXXFLAGS:-} -fsanitize=address -fsanitize=undefined -fno-sanitize=vptr,function -fno-omit-frame-pointer -g"
  export CXXFLAGS
  echo "build-soplex.sh: sanitizer enabled, CXXFLAGS=$CXXFLAGS"
fi

# CMake reads CXXFLAGS only at first configure, so toggling sanitize on
# a pre-configured `build-soplex/` would silently reuse the stale cache.
# Detect that here so a local dev does not get a half-instrumented build.
if [ -f "$BUILD_DIR/CMakeCache.txt" ]; then
  if grep -q 'fsanitize=address' "$BUILD_DIR/CMakeCache.txt"; then
    HAVE_SAN=1
  else
    HAVE_SAN=0
  fi
  if [ "$WANT_SAN" != "$HAVE_SAN" ]; then
    echo "ERROR: $BUILD_DIR/CMakeCache.txt was configured with sanitizer=$HAVE_SAN" >&2
    echo "       but LEAN_SOPLEX_SANITIZE asks for sanitizer=$WANT_SAN." >&2
    echo "       Remove $BUILD_DIR and re-run." >&2
    exit 1
  fi
fi

# CMake configure. Exact-mode flags are pinned here. PAPILO (a separate
# presolver dependency) and MPFR are disabled for the v0 bring-up; ZLIB
# is disabled because nothing in our FFI surface reads compressed files.
cmake \
  -S "$SRC_DIR" \
  -B "$BUILD_DIR" \
  -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_POSITION_INDEPENDENT_CODE=ON \
  -DBOOST=ON \
  -DGMP=ON \
  -DPAPILO=OFF \
  -DMPFR=OFF \
  -DBUILD_TESTING=OFF \
  -DZLIB=OFF

# Build only the static library target; we don't need SoPlex's CLI.
cmake --build "$BUILD_DIR" --target libsoplex --parallel

LIB="$BUILD_DIR/lib/libsoplex.a"
if [ ! -f "$LIB" ]; then
  echo "ERROR: expected $LIB after CMake build" >&2
  exit 1
fi

# Extract object files into $OBJS_DIR. `ar x` writes into cwd, so we cd
# in. Clear stale .o files first so a rebuild after a SoPlex version bump
# does not leave orphaned objects behind.
mkdir -p "$OBJS_DIR"
find "$OBJS_DIR" -maxdepth 1 \( -name '*.o' -o -name '*.obj' \) -delete
( cd "$OBJS_DIR" && ar x "$LIB" )

# Sanity check. SoPlex is heavily template-based; `libsoplex.a` only
# contains the small handful of non-template implementation files
# (around 10 .o on a current release). Most template code is
# instantiated when the bridge `.cpp` files include the SoPlex
# headers. A count under 5 indicates a broken extract.
N="$(find "$OBJS_DIR" -maxdepth 1 \( -name '*.o' -o -name '*.obj' \) | wc -l | tr -d ' ')"
if [ "$N" -lt 5 ]; then
  echo "ERROR: only $N object files extracted; expected at least the SoPlex non-template impls" >&2
  exit 1
fi

touch "$OBJS_DIR/.ready"
echo "SoPlex build complete: $N objects extracted into $OBJS_DIR"
