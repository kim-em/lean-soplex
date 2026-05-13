#!/usr/bin/env bash
# Plant LLVM compiler-rt sanitizer archives into Lean's bundled clang
# so a `LEAN_SOPLEX_SANITIZE=1 lake build -Ksanitize=1 …` link can find
# `libclang_rt.asan_static.a` and friends.
#
# Lean ships clang without compiler-rt's sanitizer runtimes, and the
# version of clang it ships changes from one Lean release to the next.
# This script detects Lean's clang major version at runtime, installs
# the matching `libclang-rt-N-dev` from apt if it is not already
# present, and symlinks the runtime archives into the directory Lean's
# clang searches.
#
# Lean's clang was built with `LLVM_ENABLE_PER_TARGET_RUNTIME_DIR=ON`,
# so it looks for `lib/x86_64-unknown-linux-gnu/libclang_rt.asan_static.a`
# etc. Both Ubuntu's distro `libclang-rt-N-dev` and apt.llvm.org's
# Debian build of the same package install in the *legacy* layout:
# `lib/linux/libclang_rt.asan-x86_64.a` etc. The script bridges by
# symlinking each `libclang_rt.<name>-x86_64.<ext>` → `libclang_rt.<name>.<ext>`,
# and also aliases the legacy preinit archive as the per-target
# `asan_static` archive (the legacy preinit archive contains the
# equivalent ELF .preinit_array hooks the per-target driver consumes).
#
# Idempotent: a second run on an already-planted toolchain is a no-op.
# Requires sudo on Linux only when the runtime package needs installing.
#
# Linux/x86_64 only — the macOS and Windows CI jobs do not exercise
# the sanitizer build. Other architectures need to extend the
# x86_64-specific rename rules below.

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

# Lean's clang stores its resource files at lib/clang/<MAJOR>/…; pick
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

# Find an installed legacy-layout asan runtime archive for clang-N.
# `libclang_rt.asan-x86_64.a` is the canonical filename in the legacy
# layout shipped by `libclang-rt-N-dev`.
find_legacy_asan() {
  find /usr/lib -name 'libclang_rt.asan-x86_64.a' \
    -path "*/clang/${CLANG_VER}/*" 2>/dev/null | head -1
}

SRC_FILE="$(find_legacy_asan)"
if [ -z "$SRC_FILE" ]; then
  echo "compiler-rt for clang-$CLANG_VER not installed; running apt-get."
  pkg="libclang-rt-${CLANG_VER}-dev"
  if ! sudo apt-get install -y "$pkg" 2>/dev/null; then
    echo "$pkg not in default repos; bootstrapping apt.llvm.org for clang-$CLANG_VER."
    TMP_SH="$(mktemp)"
    curl -fsSL -o "$TMP_SH" https://apt.llvm.org/llvm.sh
    chmod +x "$TMP_SH"
    sudo "$TMP_SH" "$CLANG_VER"
    sudo apt-get install -y "$pkg"
    rm -f "$TMP_SH"
  fi
  SRC_FILE="$(find_legacy_asan)"
fi

if [ -z "$SRC_FILE" ]; then
  echo "ERROR: compiler-rt for clang-$CLANG_VER not present after install." >&2
  echo "Files in /usr/lib/clang and /usr/lib/llvm-${CLANG_VER}:" >&2
  find /usr/lib/clang /usr/lib/llvm-"${CLANG_VER}" -name 'libclang_rt.*' 2>/dev/null \
    | head -50 >&2
  exit 1
fi

SRC="$(dirname "$SRC_FILE")"
echo "compiler-rt source: $SRC"
mkdir -p "$DEST"

# Rename `libclang_rt.<name>-x86_64.<ext>` → `libclang_rt.<name>.<ext>`.
# The per-target driver in modern clang strips the `-x86_64` arch
# suffix from runtime archive names because the arch is implied by
# the resource-dir path.
shopt -s nullglob
for src in "$SRC"/libclang_rt.*-x86_64.*; do
  base="$(basename "$src")"
  # `${base//-x86_64/}` is fine — every legacy archive embeds the
  # suffix exactly once between `<name>` and the `.a` / `.so` ext.
  newname="${base//-x86_64/}"
  ln -sfn "$src" "$DEST/$newname"
done

# Clang ≥ 17 expects `libclang_rt.asan_static.a` separately from
# `libclang_rt.asan.a`; in legacy layout the equivalent preinit hooks
# live in `libclang_rt.asan-preinit-x86_64.a`, so alias that file
# under both the renamed-legacy name and the per-target name.
preinit="$SRC/libclang_rt.asan-preinit-x86_64.a"
if [ -f "$preinit" ]; then
  ln -sfn "$preinit" "$DEST/libclang_rt.asan_static.a"
fi

N="$(ls "$DEST" | wc -l | tr -d ' ')"
echo "Planted $N files into $DEST."
# `set -o pipefail` would turn `ls | head` into a SIGPIPE failure on a
# large directory, so emit a fixed-size sample without piping.
ls -la "$DEST" >/tmp/sanitizer-runtime-listing.txt
head -30 /tmp/sanitizer-runtime-listing.txt
