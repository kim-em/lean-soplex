# lean-soplex

Lean 4 FFI bindings for [SoPlex](https://soplex.zib.de/), the linear
programming solver from the SCIP optimization suite.

The library exposes exact-mode and floating-point LP solves, MPS / LP
file I/O, and a **pure-Lean certificate checker**. Exact certificates
returned by SoPlex are treated as oracle output and checked in Lean
before any proof-carrying result is constructed. See [`PLAN.md`](./PLAN.md)
for the full design and trust model.

## Status

Pinned SoPlex tag: **`v8.0.2`** (vendored as a git submodule under
[`soplex/`](./soplex)).

Pinned Lean toolchain: see [`lean-toolchain`](./lean-toolchain).

## Build

System dependencies:

| Platform | Packages |
|----------|----------|
| Linux    | `cmake ninja-build libgmp-dev libgmpxx4ldbl libboost-dev` |
| macOS    | `brew install gmp boost cmake ninja` |
| Windows  | MSYS2 `mingw-w64-x86_64-{gcc,cmake,ninja,make,gmp,boost}` |

Clone with submodules and run the SoPlex build script once, then `lake
build`:

```bash
git clone --recurse-submodules https://github.com/kim-em/lean-soplex
cd lean-soplex
# Windows MSYS2 MINGW64 only: stage mingw runtime archives once.
# Skip on Linux / macOS.
[ "$OSTYPE" = "msys" ] && ./scripts/stage-mingw-libs.sh
./scripts/build-soplex.sh    # compiles SoPlex via its bundled CMake
lake build soplex-smoke      # builds the Lean binding + smoke test
./.lake/build/bin/soplex-smoke
```

The smoke test prints SoPlex's version, solves a toy LP, and exits 0
on success. The verifier-only target can be built separately with
`lake build LeanSoplexVerify`; it does not require the FFI library.

The first `build-soplex.sh` invocation is slow (~1–3 min to compile
SoPlex). Subsequent runs are nearly instant — CMake reuses its cache,
and Lake only recompiles the bridge if its `.cpp` files change.

## Trust model

`lean-soplex` exposes two parallel libraries:

* **`LeanSoplex.Verify`** — a pure-Lean certificate checker that
  validates LP optimality / infeasibility / unboundedness certificates
  against a `Problem` value. No FFI dependency; depends only on core
  Lean. Consumers that only want the checker (e.g. to validate
  certificates produced elsewhere) can depend on this target alone.

* **`LeanSoplex`** — the FFI binding to SoPlex. Treated as an
  unverified oracle. Every certificate it produces is checked
  in pure Lean before any proof is constructed.

A bug anywhere in SoPlex, the C++ bridge, or the sign-convention
translation can only cause a verifier rejection
(`Verified.unchecked`), not a wrong proof. See `PLAN.md` §
"Verification layer".

## Layout

```
soplex/                       # vendor submodule (scipopt/soplex, tag v8.0.2)
ffi/lean_soplex.cpp           # C++ glue calling into SoPlex
ffi/lean_soplex_bridge.cpp    # extern "C" entry points Lean calls
ffi/lean_soplex.h             # C ABI between the two .cpp files above
LeanSoplex/Basic.lean         # opaque FFI declarations + solver/file I/O API
LeanSoplex/Verify.lean        # pure-Lean certificate checker
Main.lean                     # smoke-test executable
lakefile.lean                 # Lake build config (two lean_lib targets)
scripts/build-soplex.sh       # invokes SoPlex's CMake, extracts objects
scripts/install-toolchain.sh  # elan + GitHub-fallback toolchain installer
.github/workflows/ci.yml      # Linux + macOS + Windows CI matrix
```

## CI

Every push and PR runs the build on Linux, macOS, and Windows. The
matrix is non-negotiable: certificate checkers, FFI object lifetimes,
and GMP linkage all break silently on a subset of platforms.

## Licence

`lean-soplex` is licenced under the [Apache License 2.0](./LICENSE),
matching SoPlex itself. The compiled binary's GMP runtime dependency
(LGPL) is linked dynamically by default — see [`PLAN.md`](./PLAN.md) §
"System dependencies" for the static-vs-dynamic trade-offs.
