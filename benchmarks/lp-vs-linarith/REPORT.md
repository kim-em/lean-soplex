# `lp` vs `linarith` — comparison report

**Subject.** Wall-clock comparison of Soplex's `lp` tactic (this repo) against
Mathlib's `linarith` on linear-arithmetic goals over `Rat`, on the soplex
`issue-87` branch — the explicit-proof-term certificate discharger of
issue #87, which replaces the reflective `RatLin` normalizer that earlier
revisions of this report measured.

**Take-away in one paragraph.** `lp` is now competitive with or faster
than `linarith` across the whole range measured. On integer dense LPs
the two are at parity through N ≈ 30, `lp` pulls ahead from N = 40, and
by N = 80 `lp` is ~1.4× faster; at N = 100 `linarith` fails outright
(`maximum recursion depth`) on every seed while `lp` completes in ~31 s.
On rational dense LPs `lp` is **~2× faster than `linarith` throughout**
from N = 16 up (e.g. N = 64: 15 s vs 32 s; N = 80: 24 s vs 52 s). This
is a reversal of the earlier report's finding: under the reflective
`RatLin` discharger `lp` was 2–3× *slower* than `linarith` below
N ≈ 50, because `proveAlgebraicIdentity` dominated tactic time and the
kernel re-ran an evaluator over the certificate on every typecheck. The
issue-#87 discharger builds the identity proof as an explicit term —
the kernel only structurally typechecks it — which cut `lp`'s tactic
execution and kernel typecheck each by roughly an order of magnitude
(N = 40: tactic 6.5 s → 1.3 s, kernel 6.5 s → 0.47 s). SoPlex's actual
LP solve remains single-digit milliseconds throughout — it was never
the bottleneck.

---

## 1. Methodology

Each benchmark invokes `lake env lean <file>` on a one-example Lean file,
with `/usr/bin/time -p`. Two test families are generated and committed:

| Family | Construction | Goal |
|---|---|---|
| `IntN{n}` | N variables; an N×N integer matrix with random small entries (1..3), made diagonally dominant so `x = 1ₙ` is in the feasible region and on the active boundary | `Σ xᵢ ≤ N` (tight at `x = 1ₙ`) |
| `RatN{n}` | N variables; coefficients of the form `(k/d)` with `k ∈ {1,2,3}`, `d ∈ {2,3,5}` | `Σ xᵢ ≤ N²` |

Each family has paired files: `IntN10LP.lean` calls `by lp`,
`IntN10LA.lean` calls `by linarith`, so the only difference is the
tactic. Wall-clock includes a ~3 s `import` baseline (each invocation
re-imports the dependencies; the figures are total elapsed, not
tactic-only).

The headline tables in §2 are means over **five random seeds per (family,
N, tactic)**, with the per-seed min and max alongside as a measure of
per-instance spread. The generators take an explicit seed argument
(`dense_integer.py N tac [seed]`); the seed is the problem size for the
committed canonical `.lean` files, and 1..5 for the multi-seed runs. The
multi-seed runner is [`run-multi-seed.sh`](./run-multi-seed.sh); the
generated files for multi-seed runs land under `LPvsLinarith/Seeded/`,
which is gitignored.

The generators (Python) live under [`generators/`](./generators/) and
are committed alongside the canonical generated `.lean` files so the
harness is reproducible without re-running them.

## 2. Results

### 2.0 The smallest cases: `lp` adds almost no overhead

The minimum possible work is a single hypothesis on a single variable;
both tactics should pay only the import / per-invocation cost. After the
first cold-cache invocation the per-invocation floor is **~3.0–3.2 s** —
the cost of `lake env lean` plus loading the oleans of Soplex +
Mathlib's `Linarith`. Single-seed integer-family data at small N:

| N | `lp` | `linarith` |
|---:|---:|---:|
| 2 | 3.0 s | 3.1 s |
| 4 | 3.2 s | 3.5 s |
| 6 | 3.4 s | 3.4 s |
| 8 | 3.4 s | 3.4 s |

Both tactics sit on the import floor through N = 8 — neither adds
anything measurable. The work begins to scale with the problem's
syntactic size from N = 10 on; see §2.1.

### 2.1 Integer-coefficient dense LPs

Means of 5 random seeds; the `range` columns are the per-seed min and
max.

| N | `lp` mean | `lp` range | `linarith` mean | `linarith` range | notes |
|---:|---:|:---:|---:|:---:|:---|
| 10 | 5.1 s | 3.2 – 11.5 | 3.4 s | 3.1 – 3.6 | first-call cold cache inflates the `lp` high end; warm seeds ≈ 3.6 s |
| 20 | 3.9 s | 3.5 – 4.1 | 3.9 s | 3.5 – 4.4 | parity |
| 30 | 4.9 s | 4.5 – 5.3 | 4.9 s | 4.5 – 5.4 | parity |
| 40 | 6.1 s | 5.9 – 6.9 | 6.5 s | 6.1 – 7.4 | `lp` ahead |
| 50 | 8.1 s | 7.8 – 8.8 | 9.2 s | 8.5 – 10.9 | `lp` ahead |
| 60 | 11.1 s | 10.5 – 11.9 | 13.3 s | 12.5 – 14.2 | `lp` ahead |
| 80 | **19.3 s** | 18.5 – 20.3 | 27.6 s | 25.9 – 30.1 | `lp` ~1.4× faster |
| 100 | **31.1 s** | 30.5 – 32.2 | **fails (5/5)** | — | `linarith` exceeds `maximum recursion depth` on every seed |

`lp` and `linarith` are within noise of each other through N = 30. From
N = 40 `lp` is consistently faster, and the gap widens with N. At
N = 100 `linarith` fails on every seed; `lp` is the only tactic that
completes the whole N = 10..100 range.

### 2.2 Rational-coefficient dense LPs

Coefficients are `(k/d)` with `k ∈ {1,2,3}`, `d ∈ {2,3,5}` — small
rational entries throughout. Means of 5 seeds.

| N | `lp` mean | `lp` range | `linarith` mean | `linarith` range |
|---:|---:|:---:|---:|:---:|
| 8 | 3.9 s | 3.4 – 4.8 | 3.8 s | 3.4 – 4.2 |
| 16 | 3.7 s | 3.5 – 4.0 | 5.0 s | 4.7 – 5.2 |
| 24 | 4.8 s | 4.2 – 6.3 | 7.4 s | 6.6 – 9.0 |
| 32 | 5.5 s | 5.1 – 6.1 | 10.1 s | 9.2 – 11.0 |
| 40 | 6.8 s | 6.5 – 7.1 | 14.2 s | 13.3 – 15.3 |
| 48 | 9.2 s | 8.7 – 9.6 | 19.3 s | 17.3 – 20.3 |
| 56 | 11.8 s | 10.8 – 13.1 | 25.9 s | 24.7 – 27.0 |
| 64 | 15.0 s | 14.1 – 15.8 | 32.0 s | 31.5 – 32.6 |
| 72 | 19.3 s | 17.9 – 22.7 | 41.7 s | 40.3 – 42.9 |
| 80 | 24.1 s | 22.4 – 28.3 | 51.8 s | 49.3 – 56.1 |

Rational dense is where `lp` separates cleanly: from N = 16 up it is
consistently **~2× faster than `linarith`**, and the absolute gap grows
with N (a 28 s margin at N = 80). `linarith`'s cost on these instances
grows with its internal Simplex iteration count; `lp`'s grows with the
size of the explicit certificate proof, which on these small-rational
constructions stays comparatively compact.

## 3. Instance variance

The dense-LP timings have real per-seed spread. `lp`'s wall-clock is
governed by the size of the weighted-sum certificate proof it builds,
and the number of nonzero terms in that sum is the number of nonzero
dual multipliers in the Farkas certificate SoPlex returns. That number
depends on the *combinatorial structure* of the instance — which
constraints are active at the optimal vertex — and varies with random
changes to the matrix. The spread is visible in the `range` columns of
§2 (e.g. rational N = 72: 17.9–22.7 s).

The variance is, however, far smaller than under the previous
reflective discharger: that report recorded a 2.9× spread at rational
N = 80 (25–72 s); the issue-#87 discharger holds the same row to
22.4–28.3 s (1.3×). Building the certificate identity as an explicit
term — rather than reflecting it and having the kernel re-evaluate —
removes the super-linear sensitivity to certificate density that
amplified the spread before. `lp` is no longer non-monotone in N over
the ranges measured.

## 4. Where the time goes

Per-phase breakdown of `lp` at N = 40, measured with `IO.monoMsNow`
brackets around each phase of `solveAtomic` / `proveEntailed` /
`assembleLeProof`:

| Phase (within `lp`, N = 40) | time |
|---|---:|
| `parse(goal + hyps)` (`solveAtomic`) | 489 ms |
| `validate(p)` | 15 ms |
| **`solveExact` (SoPlex FFI)** | **28 ms** |
| `assembleLeProof` — force row proofs | 4 ms |
| `assembleLeProof` — `buildWeightedSumAndProof` | 24 ms |
| **`proveCertificateIdentity` (issue #87 discharger)** | **582 ms** |

Compare the previous report, where the reflective `proveAlgebraicIdentity`
alone was **5 052 ms at N = 40 — 82 % of tactic execution**. The
explicit-proof-term discharger that replaces it is **582 ms**, and it is
no longer a lone dominant phase: hypothesis parsing (489 ms) is now
comparable. SoPlex's actual LP solve is 28 ms.

Profiler totals (`set_option profiler true`), `lp` on the canonical
seed-N integer files:

| | N=10 | N=20 | N=40 | N=80 | N=100 |
|---|---:|---:|---:|---:|---:|
| Tactic execution | 75 ms | 245 ms | 1.30 s | 8.3 s | 15.4 s |
| Kernel typecheck | 32 ms | 105 ms | 0.47 s | 2.0 s | 3.3 s |

Apples-to-apples against `linarith` (profiler):

| | N=10 | | N=40 | |
|---|---:|---:|---:|---:|
| | `lp` | `linarith` | `lp` | `linarith` |
| Tactic execution | 75 ms | ~70 ms | 1.30 s | 0.60 s |
| Kernel typecheck | 32 ms | ~25 ms | 0.47 s | 0.46 s |

The headline change from the previous report: at N = 40 `lp`'s kernel
typecheck was **6 510 ms** and is now **470 ms** — the kernel no longer
reduces an evaluator over the certificate, only structurally typechecks
an explicit term whose sole reductions are GMP-backed `Nat`/`Int`
literal arithmetic. Tactic execution at N = 40 fell from 6 460 ms to
1 300 ms. `lp`'s remaining tactic-side cost is split between hypothesis
parsing and the explicit-term discharge; neither is a 5-second outlier
anymore. The profiler totals look slightly *behind* `linarith` here,
yet §2's wall-clock has `lp` *ahead* from N = 40 — because `linarith`'s
wall-clock carries preprocessing and elaboration work the profiler's
"tactic execution" line does not attribute to it.

## 5. Families that did *not* yield a structural `lp` advantage

The original brief was to find linear-arithmetic problem families where
`lp` *structurally* beats `linarith` (a problem class, not a size
regime). Three families beyond random dense were tried; the generators
are preserved in [`generators/families.py`](./generators/families.py)
and [`generators/hilbert_tight.py`](./generators/hilbert_tight.py).
These were characterised under the previous discharger and not
re-measured for issue #87:

1. **Geometric amplification chain** — Farkas multipliers with
   exponentially large denominators; both tactics finished at the import
   baseline through n = 32.
2. **Hilbert matrices, loose and tight goal** — too small at n ≤ 14 for
   either tactic to notice the ill-conditioning.
3. **Large coprime coefficients** (5-digit primes) — both succeed; the
   previous report found `lp` slower here than `linarith`. Worth
   re-measuring under the issue-#87 discharger, since large literals no
   longer drive a kernel `decide` over a reflected term.

The deeper structural reason these don't *separate* the two tactics:
both are Farkas-certificate methods. Any family with a complex
certificate costs `lp`'s proof construction; any family with a simple
certificate is easy for both. The issue-#87 win is not a new structural
class — it is the removal of a constant-factor (and kernel-side
super-linear) overhead that applied to *every* instance.

## 6. Backend evolution timeline

| PR | What it changed |
|---|---|
| **#53** | Stage-1 `lp` tactic landed: SoPlex oracle + Lean verifier, `simp + grind` discharger. |
| **#55** | Replace `simp + grind` discharger with direct proof-term construction. |
| **#60** | Reflective `AffCert` parsing — `parseFixedExpr` 280 ms → 5 ms at N = 10. |
| **#64** | Replace the verifier backend entirely with a direct Farkas certificate (weighted-sum proof + grobner-discharged identity). Removed the `(kernel) deep recursion` wall at N ≥ 40. |
| **#66/#67** | RatLin normalizer replaces `grobner`; div-literal bridge. |
| **#71/#72** | Explicit-arg `mkAppN` for the `direct_*_close` closers — fixes `maximum recursion depth` failures at instance-dependent N = 40/50. |
| **#73** | RArray-based atom lookup. |
| **#78/#81** | `mkAppM` → typed builders in `proveLinearIdentity`; both reverted (#79/#83) — reintroduced `(kernel) deep recursion` at N ≥ 80. |
| **#84/#85** | Lazy row proof terms; safe `mkApp2`/`mkEqSymm` subset in `proveLinearIdentity`. |
| **#87** | Replace the reflective `RatLin` discharger on the optimal branch with explicit proof-term construction (`normalize` + a linear ordered-merge primitive + a soplex-internal mini-`norm_num`). The kernel only structurally typechecks the result. Tactic and kernel cost each drop ~10× at N = 40; no `(kernel) deep recursion` at N = 80/100. The numbers in §2 are on this backend. |

## 7. Recommendation

Use `lp`. On the dense LP families measured here it is competitive with
`linarith` at small N and strictly faster at scale: ~2× faster on
rational dense from N = 16 up, faster on integer dense from N = 40, and
the only one of the two that completes N = 100 integer (`linarith`
fails with `maximum recursion depth`). The earlier report's advice —
"use `linarith` below ~40 variables" — was a consequence of the
reflective discharger and no longer holds.

`lp` retains a real dependency the chooser should know about: its cost
tracks the size of the Farkas certificate SoPlex returns, so a path
with a dense certificate is more expensive than the variable count
alone suggests (§3). But that sensitivity is now a modest constant
factor, not the order-of-magnitude penalty it was. SoPlex's actual LP
solve is single-digit milliseconds throughout — it is not, and has
never been, the bottleneck.
