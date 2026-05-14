# Soplex

Lean verified certificate checking for [SoPlex](https://soplex.zib.de/), the linear programming solver from the SCIP optimization suite.

This repository (`kim-em/soplex`) is the high-level Lean package. It
sits on top of [`kim-em/soplex-ffi`](https://github.com/kim-em/soplex-ffi),
which owns the vendored SoPlex build, the C++ FFI wrapper, and the
direct Lean bindings. On top of that, `Soplex` adds:

* a **pure-Lean certificate checker** (`Soplex.Verify`);
* `solveVerified`, a driver that runs SoPlex and validates its exact
  certificate against the original problem before returning a
  proof-carrying result.
* exact-mode and floating-point LP solves, plus MPS / LP file I/O
  (re-exported from `SoplexFFI`);

## Quickstart

Add `Soplex` to your `lakefile.lean`:

```lean
require Soplex from git "https://github.com/kim-em/soplex" @ "main"
```

A minimal verified solve. We maximise `3 x₀ + 5 x₁` subject to
`x₀ ≤ 4`, `2 x₁ ≤ 12`, `3 x₀ + 2 x₁ ≤ 18`, and `x₀, x₁ ≥ 0`
(textbook example; optimum is `x = (2, 6)` with objective `36`):

```lean
import Soplex
open Soplex Soplex.Verify

def lp : Problem 3 2 :=
  { c         := #v[3, 5]
    a         := #[(0, 0, 1), (1, 1, 2), (2, 0, 3), (2, 1, 2)]
    rowBounds := #v[(none, some 4), (none, some 12), (none, some 18)]
    colBounds := #v[(some 0, none), (some 0, none)] }

def main : IO Unit := do
  match solveVerified (opts := { sense := .maximize }) lp with
  | .error e  => IO.println s!"solve failed: {repr e}"
  | .ok r =>
    match r.verified with
    | .optimal x h =>
      -- `h.1 : IsFeasible r.normalized x.toArray`
      -- `h.2 : IsOptimal  r.normalized .maximize x.toArray`
      let _ := h
      IO.println s!"optimal x = {repr x.toArray}"
    | .infeasible _    => IO.println "infeasible (with Lean proof)"
    | .unbounded _ _ _ => IO.println "unbounded (with Lean proof)"
    | .unchecked s     => IO.println s!"unchecked: {repr s}"

-- We don't yet have a tactic layer using this machinery:
-- see https://github.com/kim-em/soplex/issues/40.
```

Key shape:

* `Problem m n` is indexed by `m` constraints and `n` variables, so
  every array has its size pinned in the type. `c`, `rowBounds`,
  `colBounds` are `Vector`s; `a` is a sparse `(row, col, value)` list.
* `rowBounds` and `colBounds` are `(lo, hi)` pairs with `none = ±∞`,
  covering `≤`, `=`, `≥`, ranged constraints, and boxed variables
  uniformly.
* `solveVerified` returns a `VerifiedSolve` whose `verified` field is
  either a constructor carrying a real Lean soundness proof
  (`.optimal x h`, `.infeasible h`, `.unbounded x r h`) or
  `.unchecked status` when SoPlex was undecided or the certificate
  failed to check.

This example is kept in [`QuickstartExample.lean`](./QuickstartExample.lean)
and built as `lake exe quickstart-example` so it stays in sync with
the API.

## Status

* Pinned SoPlex tag: **`v8.0.2`**, provided transitively by the
  `SoplexFFI` dependency.
* Pinned Lean toolchain: see [`lean-toolchain`](./lean-toolchain).

## Build

System dependencies:

| Platform | Packages |
|----------|----------|
| Linux    | `build-essential cmake libgmp-dev libgmpxx4ldbl libboost-dev` |
| macOS    | `brew install gmp boost cmake` (plus Xcode Command Line Tools) |
| Windows  | MSYS2 `mingw-w64-x86_64-{gcc,cmake,ninja,make,gmp,boost}` |

Clone and build through Lake:

```bash
git clone https://github.com/kim-em/soplex
cd soplex
lake exe quickstart-example
```

Lake fetches `SoplexFFI` and initialises its vendored SoPlex submodule
as part of the build — there are no submodules in this repository
itself.

`quickstart-example` runs the verified solve from the
[Quickstart](#quickstart) above and prints `optimal x = #[2, 6]`.
For a lower-level FFI-only check (SoPlex version, throw/catch ABI,
toy LP via the direct binding) use `lake exe ffi-check`.

The first Lake build is slow (~1–3 min) because the `SoplexFFI`
dependency configures and compiles vendored SoPlex with CMake.
Subsequent runs are nearly instant: CMake reuses its cache, and Lake
only rebuilds the FFI wrapper or extracted SoPlex objects when their
inputs change.

## Trust model

SoPlex is treated as an unverified oracle. Every exact certificate it
produces is checked in Lean before any proof is constructed.

A bug anywhere in SoPlex, the C++ FFI wrapper, or the sign-convention
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
Soplex.lean                   # top-level import
Soplex/Basic.lean             # high-level API + `solveVerified`
Soplex/Verify/                # pure-Lean certificate checker
  Types.lean                  #   `Problem`, `Certificate`, `Verified`
  Validate.lean               #   input normalisation
  Driver.lean                 #   compose validate + solveExact + check
  Sound.lean                  #   soundness lemmas 
  Prop.lean, Bool.lean        #   Prop/Bool views of the checker
  Arith.lean, Budget.lean     #   rational arithmetic + denominator budget
Main.lean                     # `ffi-check` executable
SoplexTest/                   # test suite (`lake exe verify-tests`, `solve-*-tests`, etc.)
tests/fixtures/               # MPS / LP test inputs
docs/accessors.md             # row-sense × column-status accessor reference
lakefile.lean                 # depends on `SoplexFFI`
scripts/install-toolchain.sh  # elan + GitHub-fallback toolchain installer
.github/workflows/ci.yml      # Linux + macOS + Windows CI matrix
```

## Licence

`Soplex` is licenced under the [Apache License 2.0](./LICENSE),
matching SoPlex itself. The compiled binary's GMP runtime dependency
(LGPL) is linked dynamically by default through `SoplexFFI`. SoPlex
itself is linked into the Lean shared library from the vendored static
archive.
