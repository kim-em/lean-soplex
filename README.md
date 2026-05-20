# Soplex

Lean verified certificate checking for [SoPlex](https://soplex.zib.de/), the linear programming solver from the SCIP optimization suite.

This repository (`kim-em/soplex`) is the high-level Lean package. It
sits on top of [`kim-em/soplex-ffi`](https://github.com/kim-em/soplex-ffi),
which owns the vendored SoPlex build, the C++ FFI wrapper, and the
direct Lean bindings. On top of that, `Soplex` adds:

* a **pure-Lean certificate checker** (`Soplex.Verify`);
* `solveVerified`, a driver that runs SoPlex and validates its exact
  certificate against the original problem before returning a
  proof-carrying result;
* exact-mode and floating-point LP solves, plus MPS / LP file I/O
  (re-exported from `SoplexFFI`);
* fast user tactics `lp` (that handles quantifier elimination) and `maximize`.

## Quickstart

Add `Soplex` to your `lakefile.lean`:

```lean
require Soplex from git "https://github.com/kim-em/soplex" @ "main"
```

We maximize `3 x₀ + 5 x₁` subject to
`x₀ ≤ 4`, `2 x₁ ≤ 12`, `3 x₀ + 2 x₁ ≤ 18`, and `x₀, x₁ ≥ 0`
(textbook example; optimum is `x = (2, 6)` with objective `36`):

```lean
import Soplex
open Soplex Soplex.Verify

-- Proving theorems via `lp` is usually faster than Mathlib's `linarith`.
example (x₀ x₁ : Rat) (_ : x₀ ≤ 4) (_ : 2 * x₁ ≤ 12) (_ : 3 * x₀ + 2 * x₁ ≤ 18)
    (_ : 0 ≤ x₀) (_ : 0 ≤ x₁) : 3 * x₀ + 5 * x₁ ≤ 36 := by lp

-- We can also solve linear arithmetic problems involving quantifiers.
example : ∃ x : Rat, 0 ≤ x ∧ x ≤ 3 ∧
    ∀ y : Rat, x ≤ y → y ≤ 5 → y ≤ 2 * x := by lp

-- And it's also a computational library that generates certificates
-- for linear programming problems:

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

This example is kept in [`Examples/Quickstart.lean`](./Examples/Quickstart.lean)
and built as `lake exe quickstart-example` so it stays in sync with
the API.

## Tactics

The verified pipeline is exposed as two `Rat`-affine tactics that
build kernel proof terms — no `Problem`/`Certificate` data reaches the
kernel, only a weighted-sum-of-hypotheses identity discharged by an
explicit-proof-term constructor.

### `lp` 

```lean
import Soplex

example : (1 : Rat) < 2 := by lp

example (a b : Rat) (_ : 2 * a + b ≤ 5) (_ : a - b ≤ 1) :
    3 * a ≤ 6 := by lp

example (a : Rat) (_ : a ≤ 0 ∧ 0 ≤ a) : a = 0 := by lp

example (x : Rat) (_ : x ≤ 0) : x < 1 := by lp

example : ∃ x : Rat, 0 ≤ x ∧ x ≤ 1 := by lp

example : ∃ x : Rat, ∀ y : Rat, 0 ≤ y → y ≤ 1 → x ≥ y := by lp

example : ∃ x : Rat, 0 ≤ x ∧ x ≤ 3 ∧
    ∀ y : Rat, x ≤ y → y ≤ 5 → y ≤ 2 * x := by lp
```

Hypotheses that are not non-strict `Rat`-affine are silently ignored
(strict hypotheses are rejected with a tactic-level diagnostic). When
SoPlex returns infeasible, `lp` derives `False` from the dual and
closes any goal.

`lp` handles a Π₂ fragment of linear rational arithmetic. Atoms are
`Rat`-affine (in)equalities (`≤`, `<`, `=`, `≥`, `>`) in the
`Rat`-typed locals; these combine under `∧`, under `∃ x : Rat`, and
under inner `∀ y : Rat, g₁ → … → gₖ → b` whose guards `gᵢ` and body
`b` are themselves `Rat`-affine atoms — including guards that mention
the outer existential witness. The local context contributes
non-strict linear `Rat` hypotheses; SoPlex serves as an untrusted
oracle for Farkas / dual multipliers, and the kernel proof is
reconstructed from those multipliers and the original hypothesis
terms.

### `maximize` 

`maximize <expr>` runs a sup-LP over the local hypotheses and injects
`hbound : <expr> ≤ N` where `N` is the certified maximum. Use
`maximize h : <expr>` to choose the hypothesis name.

```lean
example (x₀ x₁ : Rat) (_ : 0 ≤ x₀) (_ : 0 ≤ x₁) (_ : x₀ ≤ 4)
    (_ : 2 * x₁ ≤ 12) (_ : 3 * x₀ + 2 * x₁ ≤ 18) :
    3 * x₀ + 5 * x₁ ≤ 36 := by
  maximize 3 * x₀ + 5 * x₁
  exact hbound

example (x : Rat) (_ : 0 ≤ x) (_ : x ≤ 4) : 3 * x + 7 ≤ 19 := by
  maximize h : 3 * x + 7
  exact h
```

If hypotheses are inconsistent, `maximize` closes the surrounding
goal by `False.elim`. If the LP is unbounded above, it fails without
producing a proof.

## Build

Pinned SoPlex tag: **`v8.0.2`** (transitive via `SoplexFFI`). Pinned
Lean toolchain: see [`lean-toolchain`](./lean-toolchain).

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
lake test
```

Lake fetches `SoplexFFI` and initializes its vendored SoPlex submodule
as part of the build — there are no submodules in this repository
itself.

`quickstart-example` runs the verified solve from the
[Quickstart](#quickstart) above and prints `optimal x = #[2, 6]`.
`lake test` builds and runs the full test suite under
[`SoplexTest/`](./SoplexTest). The suite includes
`SoplexTest/FFIProbe.lean`, which calls `solveVerified` from inside a
tactic and checks the elaboration-time FFI loading path used by future
tactics. For a lower-level FFI-only check
(SoPlex version, throw/catch ABI, toy LP via the direct binding) use
`lake exe ffi-check`.

The first Lake build is slow (~1–3 min) because the `SoplexFFI`
dependency configures and compiles vendored SoPlex with CMake.
Subsequent runs are nearly instant: CMake reuses its cache, and Lake
only rebuilds the FFI wrapper or extracted SoPlex objects when their
inputs change.

## Trust model

SoPlex is treated as an unverified mathematical oracle. Every exact
certificate it produces is checked in Lean before any proof is
constructed. Incorrect certificates, including certificates affected by
solver bugs or sign-convention translation mistakes, are rejected by
the Lean checker and reported as `Verified.unchecked`.

The native C++ FFI remains part of the runtime trusted computing base.
It is trusted to run safely in-process, preserve memory safety and ABI
correctness, and faithfully marshal Lean-side `Problem` and
certificate data. The Lean checker protects the mathematical proof
boundary; it does not make arbitrary native memory-safety or ABI
failures harmless.

### Verification Notes

* `solveVerified` validates and normalizes the Lean-side `Problem`,
  forces `Options.presolve := false`, runs exact-mode SoPlex, and
  checks the returned certificate against the **normalized Lean-side
  problem** — never against data round-tripped through C++. `Verified`
  is indexed by that normalized problem and the objective sense;
  `.optimal` / `.infeasible` / `.unbounded` carry real Lean proofs,
  and `.unchecked` covers undecided solver statuses and failed checks.
* Direct `solveExact` calls may use SoPlex presolve; the verified
  path forces it off. Reconstructing certificates for the original
  problem from presolve output is outside this verified path.
* Dual multipliers are stored as a nonnegative lower/upper split per
  row and column. This is more explicit than a signed dual vector
  and handles ranged rows and boxed columns uniformly.
* Maximization reduces internally to minimization by negating the
  objective; user-facing objectives and witnesses, including
  `objOffset`, stay in the caller's original sense.
* The denominator budget caps the combined numerator + denominator
  bit length of every certificate rational. Default `some 10000`;
  exceeding it yields `Verified.unchecked .budgetExceeded`. Pass
  `none` to disable.

## Layout

```
Soplex.lean                   # top-level import
Soplex/Basic.lean             # high-level API + `solveVerified`
Soplex/LP/Core.lean           # backend abstraction + registry
Soplex/Backend/SoplexFFI.lean # SoPlex FFI backend adapter
Soplex/Tactic/                # `lp` and `maximize` tactics
  LP.lean                     #   tactic frontend (elaboration + dispatch)
  Q.lean                      #   kernel-reducible rational literals for tactic proofs
Soplex/Verify.lean            # verifier re-export module
Soplex/Verify/                # pure-Lean certificate checker
  Types.lean                  #   `Problem`, `Certificate`, `Verified`
  Validate.lean               #   input normalization
  Driver.lean                 #   compose validate + solveExact + check
  Sound.lean                  #   soundness lemmas 
  Prop.lean, Bool.lean        #   Prop/Bool views of the checker
  Arith.lean, Budget.lean     #   rational arithmetic + denominator budget
Main.lean                     # `ffi-check` executable
Examples/Quickstart.lean      # quickstart example executable
SoplexTest/                   # test suite (run via `lake test`)
  Common.lean                 #   shared test scaffolding (`Soplex.Verify` only)
  SolveCommon.lean            #   adds `Soplex` for SoPlex-backed tests
  FFIProbe.lean               #   elaboration-time FFI loading regression probe
  LP*.lean                    #   tactic frontend and proof-term tests
  Solve*.lean, Verify.lean    #   solver and verifier regression tests
  AccessorGoldens.lean        #   accessor documentation golden tests
  FileIo.lean                 #   LP/MPS file-input tests
  Runner.lean                 #   `lake test` driver
  fixtures/                   #   MPS / LP test inputs
docs/accessors.md             # row-sense × column-status accessor reference
docs/backend-abstraction.md   # backend split and registry notes
docs/lp-expr-construction-inventory.md
                              # tactic expression construction notes
lakefile.lean                 # depends on `SoplexFFI`
scripts/install-toolchain.sh  # elan + GitHub-fallback toolchain installer
scripts/install-sanitizer-runtime.sh
                              # CI sanitizer runtime installer
.github/workflows/ci.yml      # Linux + macOS + Windows CI matrix
```

## Licence

`Soplex` is licensed under the [Apache License 2.0](./LICENSE),
matching SoPlex itself. The compiled binary's GMP runtime dependency
(LGPL) is linked dynamically by default through `SoplexFFI`. SoPlex
itself is linked into the Lean shared library from the vendored static
archive.
