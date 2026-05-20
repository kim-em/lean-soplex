# LP backend abstraction

Tracks the first step of the work described in
https://github.com/kim-em/soplex/issues/50 ("Decouple the verifier
and tactic from SoPlex; design a backend abstraction").

## What landed

* `Soplex.LP.Core` — the `LPBackend` record, a process-global
  registry (`backendRegistry`), and the helpers `registerBackend`,
  `resolveBackend`, `availableBackends` (which probes registered
  backends and returns them sorted by `(defaultPriority, name)`).
* `Soplex.Backend.SoplexFFI` — the FFI binding adapter. Exports
  `def backend : LPBackend` with priority `10` and self-registers
  on import via an `initialize` block.
* `Soplex.solveVerifiedWith` — backend-pluggable counterpart of
  `solveVerified`. Same pipeline (`validateOptions` → `validate` →
  `solveExact` → `verifyOutcome`), but dispatches the solve through
  the supplied `LPBackend`. Lives in `IO` because backends are
  `IO`-typed so a future subprocess or remote solver can plug in.
* `import Soplex` continues to give you the FFI backend with no
  configuration — the meta-module imports
  `Soplex.Backend.SoplexFFI`, which triggers registration.

The existing `Soplex.solveVerified` is unchanged: it still calls
`SoplexFFI.solveExact` synchronously and returns `Except`. That is
the source-level compatibility surface for current callers
(`QuickstartExample.lean`, `SoplexTest/*`, the benchmarks).

## What is deliberately *not* in this PR

* **Package split.** `lp-core`, `lp-verify`, `lp-tactic`, and
  per-backend packages are still a single `lean-soplex` package
  with one `moreLinkArgs`. Splitting requires moving the data
  vocabulary out of `SoplexFFI.Types`, which lives in a separate
  repo and is a multi-step migration.
* **Tactic backend selection.** `Soplex.Tactic.LP` still calls
  `solveExact` directly. Threading an `LPBackend` through every
  call site (and adding the `lp (backend := ...)` syntax, the
  `lp.backend` option, and the `availableBackends` fallback)
  is the natural next PR.
* **JSON and pure-Lean backends.** No work here. They become
  meaningful only after the package split decouples them from
  SoPlex's native build matrix.
* **No-FFI CI lane.** Same reason — until the package split, every
  module still transitively imports `SoplexFFI.Basic`.

## Backend record

```lean
structure LPBackend where
  name : String
  defaultPriority : Nat := 100
  solveExact : {m n : Nat} → Options → Problem m n →
               IO (Except SolveError (Solution m n))
  probe : IO (Except String Unit) := pure (.ok ())
```

Reserved priority bands (lower runs first):

* `10`   — fast native binding (FFI),
* `50`   — out-of-process subprocess (JSON),
* `100`  — pure-Lean reference,
* `1000` — experimental / opt-in.

## Registry semantics

* `registerBackend b` raises on duplicate `name`. To replace a
  backend, callers should pass an explicit value through
  `solveVerifiedWith` (or, once it exists, `lp (backend := ...)`).
* `initialize` blocks insert the descriptor; they never run the
  probe. Probes only run when fallback iteration is consulted.
* `availableBackends` returns a freshly sorted array every call.
  Do not rely on `Std.HashMap` iteration order.
* A backend whose `probe` raises an `IO` exception is treated as
  probe-failed with the exception message in the error.

## Adding a new backend (once the package split happens)

1. Create the backend module (`Soplex.Backend.Foo`).
2. Define `def backend : LPBackend := { name := "foo", … }`.
3. Self-register: `initialize registerBackend backend`.
4. Pick a priority band; if in doubt, `1000` (experimental).
5. Users importing your module get it picked up automatically;
   they can still override via `lp (backend := Foo.backend)` once
   the tactic supports that syntax.
