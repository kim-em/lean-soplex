# Soplex

Lean 4 bindings and verified certificate checking for
[SoPlex](https://soplex.zib.de/), the linear programming solver from
the SCIP optimization suite.

The library exposes exact-mode and floating-point LP solves, MPS / LP
file I/O, and a **pure-Lean certificate checker**. Exact certificates
returned by SoPlex are treated as oracle output and checked in Lean
before any proof-carrying result is constructed.

## Status

Pinned SoPlex tag: **`v8.0.2`**, provided by the
[`SoplexFFI`](https://github.com/kim-em/soplex-ffi) dependency.

Pinned Lean toolchain: see [`lean-toolchain`](./lean-toolchain).

## Build

System dependencies:

| Platform | Packages |
|----------|----------|
| Linux    | `cmake ninja-build libgmp-dev libgmpxx4ldbl libboost-dev` |
| macOS    | `brew install gmp boost cmake ninja` |
| Windows  | MSYS2 `mingw-w64-x86_64-{gcc,cmake,ninja,make,gmp,boost}` |

Clone with submodules and build through Lake:

```bash
git clone https://github.com/kim-em/soplex
cd soplex
lake exe ffi-check
```

Lake fetches `SoplexFFI` and initializes its vendored SoPlex submodule
as part of the build.

`ffi-check` prints SoPlex's version, solves a toy LP, and exits 0
on success.

The first Lake build is slow (~1–3 min) because the `SoplexFFI`
dependency configures and compiles vendored SoPlex with CMake.
Subsequent runs are nearly instant: CMake reuses its cache, and Lake
only rebuilds the bridge or extracted SoPlex objects when their inputs
change.

## Trust model

`Soplex` is layered over the `SoplexFFI` package:

* **`SoplexFFI`** — the direct SoPlex binding package. It owns the
  vendored solver build, C++ bridge, thin Lean extern wrappers,
  marshalling, direct solve APIs, and file I/O.

* **`Soplex`** — the high-level package. It re-exports the direct
  SoPlex APIs and adds `Soplex.Verify` plus `solveVerified`.

SoPlex is treated as an unverified oracle. Every exact certificate it
produces is checked in Lean before any proof is constructed.

A bug anywhere in SoPlex, the C++ bridge, or the sign-convention
translation can only cause a verifier rejection
(`Verified.unchecked`), not a wrong proof.

### Verification Notes

* `solveVerified` validates and normalises the Lean-side `Problem`,
  forces `Options.presolve := false`, calls exact-mode SoPlex, then
  checks the returned certificate against the normalised original
  problem. Certificates are never checked against data round-tripped
  through C++.
* `Verified` is indexed by the normalised problem and objective sense.
  `Verified.optimal`, `.infeasible`, and `.unbounded` carry Lean proofs;
  undecided solver statuses or failed certificates return
  `Verified.unchecked`.
* The verifier stores dual multipliers as a nonnegative lower/upper
  split for rows and columns. This is deliberately more explicit than
  a signed dual vector and handles ranged rows and boxed columns
  uniformly.
* Maximisation is reduced internally to minimisation by negating the
  objective. User-facing objectives and witnesses remain in the
  caller's original sense, including `objOffset`.
* `solveVerified` has a denominator budget, defaulting to `some 10000`
  bits per rational coordinate. Exceeding it returns
  `Verified.unchecked .budgetExceeded`; `none` disables the check.
* SoPlex presolve is allowed for direct `solveExact` calls, but is not
  part of the verified path yet. Reconstructing original-problem
  certificates from presolve is tracked separately.

## Layout

```
Soplex/Basic.lean             # high-level API + solveVerified
Soplex/Verify.lean            # pure-Lean certificate checker
Main.lean                     # `ffi-check` executable
lakefile.lean                 # high-level Lake package, depends on SoplexFFI
scripts/install-toolchain.sh  # elan + GitHub-fallback toolchain installer
.github/workflows/ci.yml      # Linux + macOS + Windows CI matrix
```

## CI

Every push and PR runs the build on Linux, macOS, and Windows. The
matrix is non-negotiable: certificate checkers, FFI object lifetimes,
and GMP linkage all break silently on a subset of platforms.

## Licence

`Soplex` is licenced under the [Apache License 2.0](./LICENSE),
matching SoPlex itself. The compiled binary's GMP runtime dependency
(LGPL) is linked dynamically by default through `SoplexFFI`. SoPlex
itself is linked into the Lean shared library from the vendored static
archive.
