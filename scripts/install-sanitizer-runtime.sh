#!/usr/bin/env bash
# Plant LLVM compiler-rt sanitizer archives into Lean's bundled clang
# so a `LEAN_SOPLEX_SANITIZE=1 lake build -Ksanitize=1 …` link can find
# `libclang_rt.asan_static.a` and friends.
#
# Lean ships clang without compiler-rt's sanitizer runtimes, and the
# version of clang it ships changes from one Lean release to the next.
# This script detects Lean's clang major version at runtime, installs
# matching upstream packages from apt.llvm.org if the per-target
# runtime is not already on the system, and symlinks the archives
# into the directory Lean's clang searches.
#
# Idempotent: a second run on an already-planted toolchain is a no-op.
# Requires sudo on Linux for `apt-get install` (only when the runtime
# isn't already installed).
#
# Linux/x86_64 only — the macOS and Windows CI jobs do not exercise
# the sanitizer build, and the LLVM apt repo is Debian/Ubuntu-only.
# Other distros / arches need to provide the runtime archives by hand.

set -euo pipefail

if [ "$(uname -s)" != "Linux" ]; then
  echo "install-sanitizer-runtime.sh: not Linux, nothing to do."
  exit 0
fi

if [ "$(uname -m)" != "x86_64" ]; then
  echo "install-sanitizer-runtime.sh: only x86_64 is wired up." >&2
  exit 1
fi

if ! command -v lean >/dev/null 2>&1; then
  echo "ERROR: lean not on PATH; install the Lean toolchain first." >&2
  exit 1
fi

LEAN_PREFIX="$(lean --print-prefix)"
LEAN_CLANG_DIR="$LEAN_PREFIX/lib/clang"
if [ ! -d "$LEAN_CLANG_DIR" ]; then
  echo "ERROR: $LEAN_CLANG_DIR not found; toolchain layout unexpected." >&2
  exit 1
fi

# Lean's clang stores its resource files at lib/clang/<MAJOR>/...; pick
# the highest version present (typically only one).
CLANG_VER="$(ls "$LEAN_CLANG_DIR" | sort -n | tail -1)"
if [ -z "$CLANG_VER" ]; then
  echo "ERROR: no version subdirectory under $LEAN_CLANG_DIR" >&2
  exit 1
fi
DEST="$LEAN_CLANG_DIR/$CLANG_VER/lib/x86_64-unknown-linux-gnu"
echo "Lean clang major version: $CLANG_VER"
echo "Planting compiler-rt into:  $DEST"

if [ -f "$DEST/libclang_rt.asan_static.a" ]; then
  echo "compiler-rt already in place; nothing to do."
  exit 0
fi

# The marker file `libclang_rt.asan_static.a` only exists in the
# per-target runtime layout Lean's clang expects. Ubuntu/Debian's
# distro `libclang-rt-N-dev` packages use the legacy layout under
# `lib/linux/` and ship `libclang_rt.asan-x86_64.a` etc. instead;
# apt.llvm.org's upstream LLVM packages use the per-target layout.
find_source() {
  find /usr/lib -name 'libclang_rt.asan_static.a' \
    -path "*/clang/${CLANG_VER}/*" 2>/dev/null | head -1
}

SRC_FILE="$(find_source)"
if [ -z "$SRC_FILE" ]; then
  echo "Per-target compiler-rt for clang-$CLANG_VER not found; installing from apt.llvm.org."
  TMP_SH="$(mktemp)"
  curl -fsSL -o "$TMP_SH" https://apt.llvm.org/llvm.sh
  chmod +x "$TMP_SH"
  sudo "$TMP_SH" "$CLANG_VER"
  sudo apt-get install -y "libclang-rt-${CLANG_VER}-dev"
  rm -f "$TMP_SH"
  SRC_FILE="$(find_source)"
fi

if [ -z "$SRC_FILE" ]; then
  echo "ERROR: per-target compiler-rt for clang-$CLANG_VER still not present." >&2
  echo "       Inspect /usr/lib/clang and /usr/lib/llvm-${CLANG_VER}." >&2
  exit 1
fi

SRC="$(dirname "$SRC_FILE")"
echo "compiler-rt source: $SRC"
mkdir -p "$DEST"
for f in "$SRC"/libclang_rt.*; do
  ln -sfn "$f" "$DEST/$(basename "$f")"
done
echo "Planted $(ls "$DEST" | wc -l | tr -d ' ') files into $DEST"
