#!/usr/bin/env bash
# Stage MSYS2 MINGW64 runtime libraries into `soplex-ffi/vendor/mingw-libs/`
# for the Windows Lake build. The lakefile references these archives by
# relative path from the `soplex-ffi` package, so we don't depend on the
# absolute location of MSYS2.
#
# Idempotent: subsequent runs overwrite. Safe to invoke unconditionally
# from CI and from local dev loops.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"

if [ -z "${MINGW_PREFIX:-}" ]; then
  echo "ERROR: MINGW_PREFIX is not set." >&2
  echo "       Run this script from an MSYS2 MINGW64 shell." >&2
  exit 1
fi

if [ ! -d "$MINGW_PREFIX/lib" ]; then
  echo "ERROR: $MINGW_PREFIX/lib does not exist." >&2
  echo "       Is MSYS2 MINGW64 fully installed?" >&2
  exit 1
fi

mkdir -p "$ROOT/vendor/mingw-libs"

# The lakefile references these archives explicitly:
#   libstdc++.a  libgmpxx.a  libgmp.a
# and resolves these via `-L vendor/mingw-libs -l*`:
#   libgcc_s  libmingwex  libmsvcrt
# The wildcard list below is broader to also stage the import-lib
# variants and ancillary archives that `-l*` may pick up.
for pat in 'libgmpxx*' 'libgmp*' 'libgcc*' 'libwinpthread*' \
           'libstdc++*' 'libmsvcrt*' 'libmingwex*' 'libmingw32*'; do
  cp "$MINGW_PREFIX/lib"/$pat "$ROOT/vendor/mingw-libs/" 2>/dev/null || true
done

# Verify the archives the lakefile references by relative path are
# actually present, so a missing file fails here (with a clear message)
# rather than during `lake build` (with a generic linker error).
for required in libstdc++.a libgmpxx.a libgmp.a; do
  if [ ! -f "$ROOT/vendor/mingw-libs/$required" ]; then
    echo "ERROR: $ROOT/vendor/mingw-libs/$required missing after staging." >&2
    echo "       Expected from $MINGW_PREFIX/lib/. Check the MSYS2" >&2
    echo "       install includes mingw-w64-x86_64-gcc and" >&2
    echo "       mingw-w64-x86_64-gmp." >&2
    exit 1
  fi
done

N="$(ls "$ROOT/vendor/mingw-libs/" | wc -l | tr -d ' ')"
echo "Staged $N runtime archives into $ROOT/vendor/mingw-libs/"
