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
