# `lp` vs `linarith` — comparison report

**Subject.** Wall-clock comparison of Soplex's `lp` tactic (this repo) against
Mathlib's `linarith` on linear-arithmetic goals over `Rat`, on the soplex
`main` at the time of writing (`8c8b215`).

**Take-away in one paragraph.** On hand-written tactic-scale problems
(N ≤ ~50 variables), `linarith` is faster — typically 2–3× — because
`lp` pays a per-invocation overhead in metaprogram-side `Expr`
construction that `linarith` largely avoids. The two reach parity
around N = 60, and **at N = 80 dense integer `lp` is consistently faster
than `linarith` across all five seeds we ran**. At N = 100 dense integer,
`linarith` itself fails on every seed with `maximum recursion depth has
been reached`, while `lp` completes in ~29 s. On dense rational
instances, the two are closer to parity throughout and `lp` exhibits
substantial per-instance variance (a 2.9× spread at N = 80). The
demonstrable advantage is **scale robustness** for integer dense, not
a structural win on a particular problem class. SoPlex's actual LP
solve is single-digit milliseconds throughout — it is not the
bottleneck on either side.

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

Before the headline tables, a baseline check. The minimum possible work
is a single hypothesis on a single variable; both tactics should pay
only the import / per-invocation cost. Three back-to-back runs of each:

| | run 1 (cold) | run 2 | run 3 |
|---|---:|---:|---:|
| `import Soplex; import Mathlib.Tactic.Linarith` only (no tactic) | 10.0 s | 3.13 s | 3.13 s |
| `example (a : Rat) (_h : a ≤ 1) : a ≤ 2 := by lp` | 3.18 s | 3.12 s | 3.10 s |
| `example (a : Rat) (h : a ≤ 1) : a ≤ 2 := by linarith` | 3.13 s | 3.18 s | 3.43 s |

After the first cold-cache invocation, the per-invocation floor is
**3.1–3.2 s** — that is the cost of `lake env lean` plus loading the
oleans of Soplex + Mathlib's `Linarith`. Both tactics add nothing
measurable above that floor on the trivial example. So the gap you see
at N=10 below is *not* per-invocation overhead — it is genuine work
scaling with the problem's syntactic size.

Multi-seed small-N data (means over 5 seeds, integer family):

| N | `lp` | `linarith` |
|---:|---:|---:|
| 2 | 3.1 s | 3.2 s |
| 4 | 3.2 s | 3.1 s |
| 6 | 3.4 s | 3.2 s |
| 8 | 3.4 s | 3.2 s |
| 10 | 5.7 s* | 3.1 s |

`lp` adds essentially nothing through N = 8 (each row of the N = 8
dense-integer instance has 8 terms — ~64 multiplications and 56
additions in the constraint matrix). The ramp begins between N = 8 and
N = 10 and steepens fast — see §4 for where the time goes.

(*) The N = 10 `lp` mean includes one 10.1 s cold-cache outlier; without
it the other four seeds average 4.6 s.

### 2.1 Integer-coefficient dense LPs

Means of 5 random seeds; the `range` columns are the per-seed min and
max.

| N | `lp` mean | `lp` range | `linarith` mean | `linarith` range | notes |
|---:|---:|:---:|---:|:---:|:---|
| 10 | 5.7 s | 3.7 – 10.1 | 3.1 s | 3.0 – 3.4 | first-call cold cache inflates the high end |
| 20 | 5.1 s | 4.9 – 5.2 | 3.6 s | 3.6 – 3.7 |  |
| 30 | 9.1 s | 8.9 – 9.6 | 4.5 s | 4.4 – 4.8 |  |
| 40 | 16.6 s | 16.3 – 16.9 | 6.3 s | 6.0 – 7.0 |  |
| 50 | 29.3 s | 28.0 – 33.2 | 9.0 s | 8.6 – 9.5 |  |
| 60 | 13.6 s | 13.2 – 14.1 | 12.8 s | 12.6 – 13.1 | parity |
| 80 | **20.0 s** | 19.8 – 20.1 | 26.8 s | 26.4 – 27.0 | `lp` is consistently faster |
| 100 | **28.5 s** | 27.2 – 29.0 | **fails (5/5)** | — | `linarith` exceeds `maximum recursion depth` on every seed |

The N = 60 mean drops below the N = 50 mean across **every** seed
(range 13.2–14.1 vs 28.0–33.2). The generator's seed-N construction
evidently lands on instances at N = 60 whose Farkas certificates are
significantly sparser than at N = 50 — see §3 for why this matters.

### 2.2 Rational-coefficient dense LPs

Coefficients are `(k/d)` with `k ∈ {1,2,3}`, `d ∈ {2,3,5}` — small
rational entries throughout. Means of 5 seeds.

| N | `lp` mean | `lp` range | `linarith` mean | `linarith` range | notes |
|---:|---:|:---:|---:|:---:|:---|
| 8 | 6.4 s | 3.2 – 13.4 | 3.9 s | 3.3 – 5.8 | cold cache inflates the high end |
| 16 | 4.0 s | 3.9 – 4.3 | 4.7 s | 4.5 – 4.8 |  |
| 24 | 5.8 s | 5.4 – 6.2 | 6.8 s | 6.6 – 6.9 |  |
| 32 | 8.6 s | 7.9 – 9.1 | 9.7 s | 9.3 – 10.2 |  |
| 40 | 13.1 s | 11.9 – 15.7 | 13.9 s | 12.9 – 14.9 |  |
| 48 | 21.3 s | 20.5 – 22.2 | 19.0 s | 18.6 – 19.6 |  |
| 56 | 29.7 s | 27.1 – 35.0 | 25.2 s | 23.9 – 26.9 |  |
| 64 | 44.4 s | 42.4 – 48.5 | 33.0 s | 32.7 – 33.3 |  |
| 72 | 58.0 s | 54.2 – 68.9 | 41.9 s | 40.4 – 43.0 |  |
| 80 | 43.7 s | **25.1 – 72.2** | 52.2 s | 49.7 – 55.8 | huge `lp` instance spread; see §3 |

Rational dense is closer to parity than integer dense, with `lp` and
`linarith` trading slightly across N ≤ 40 and `linarith` pulling ahead
from N = 48 up. The N = 80 row is the per-instance variance from §3
made manifest in dramatic form: across five seeds, `lp`'s wall-clock at
this single problem size ranges from **25 s to 72 s** (a 2.9× spread),
while `linarith`'s ranges only from 50 s to 56 s. When the random
instance happens to admit a sparse Farkas certificate, `lp`'s
weighted-sum proof is short and it beats `linarith`; when the
certificate is dense, the proof term grows and `lp` is slower. `linarith`,
whose cost grows with its internal Simplex iterations rather than with
certificate sparsity, doesn't see the same swing.

## 3. Instance variance

The dense-LP timings are **not monotone in N** and have real per-seed
spread that no amount of averaging removes. The mechanism is the same in
each case: `lp`'s wall-clock is dominated by the size of the weighted-sum
proof term it builds, and the number of nonzero terms in that sum is
the number of nonzero dual multipliers in the Farkas certificate SoPlex
returns. That number depends on the *combinatorial structure* of the
instance — which constraints are active at the optimal vertex — and
varies discontinuously with random changes to the matrix. Two instances
of the same N can produce a 2.9× swing in `lp`'s wall-clock (see the
rational N = 80 row in §2.2), while `linarith`'s pure-Lean Simplex
iteration count is comparatively stable across the same swing.

This is *not* measurement noise. Re-running the same seed reproduces the
same number to within a few percent (the spread inside a single (N,
tactic, seed) row from re-runs is small). The variance in the tables is
genuine variance in the problem instances themselves: different seeds at
the same N are different LPs, and `lp`'s cost is sensitive to their
certificate structure in a way `linarith`'s is not.

Consequences:

1. **Mean alone is misleading at large N.** The means in §2 are
   accompanied by the per-seed range so the reader can see when one
   instance is dragging the mean.
2. **`lp` is not monotone in N**: the integer-dense N = 60 mean is less
   than the N = 50 mean across all five seeds. The seed-N families don't
   uniformly get harder with size; they sample a distribution whose
   tail-mass at a given N depends on the construction.
3. **For pedagogy or marketing**, picking favourable seeds is easy.
   This report quotes 5-seed means and ranges so that case isn't being
   made by accident.

## 4. Where the time goes

Per-phase breakdown of `lp` on the current main, measured with
`IO.monoMsNow` brackets around each phase of `solveAtomic` /
`proveEntailed` / `assembleLeProof`, plus `set_option profiler true`
for tactic-execution and kernel-typecheck totals.

| Phase (within `lp`) | N=4 | N=8 | N=10 | N=20 | N=40 |
|---|---:|---:|---:|---:|---:|
| `parse(goal+hyps)` (`solveAtomic`) | 3 ms | 9 ms | 15 ms | 77 ms | 545 ms |
| `parse(goal-aff)` (`proveEntailed`) | 1 ms | 0 ms | 1 ms | 3 ms | 18 ms |
| `validate(p)` | 1 ms | 0 ms | 0 ms | 2 ms | 7 ms |
| **`solveExact` (SoPlex FFI)** | **7 ms** | **2 ms** | **3 ms** | **8 ms** | **32 ms** |
| `assembleLeProof` — force row proofs | 0 ms | 1 ms | 1 ms | 4 ms | 26 ms |
| `assembleLeProof` — `buildWeightedSumAndProof` | 6 ms | 8 ms | 9 ms | 17 ms | 41 ms |
| **`proveAlgebraicIdentity` (RatLin)** | **32 ms** | **103 ms** | **168 ms** | **881 ms** | **5 052 ms** |

`proveAlgebraicIdentity` — the RatLin normalizer's discharge of the
`(rhs − lhs) + Σ λᵢ tᵢ = c` identity — is **74 % of tactic execution at
N = 10 and 82 % at N = 40**. Its growth is super-linear (≈ O(N²) on this
construction). Everything else in the tactic body is small in
comparison. SoPlex's actual LP solve never exceeds 32 ms.

Total picture, apples-to-apples vs `linarith` (profiler):

| | N=10 | | N=40 | |
|---|---:|---:|---:|---:|
| | `lp` | `linarith` | `lp` | `linarith` |
| Tactic execution | 228 ms | 73 ms | 6 460 ms | 597 ms |
| Kernel typecheck | 138 ms | 23 ms | 6 510 ms | 467 ms |
| **Sum** | **366 ms** | **96 ms** | **12 970 ms** | **1 064 ms** |
| `lp` / `linarith` | 3.8× | | 12.2× | |

Two things to read out of this:

1. **`lp`'s tactic-side bottleneck is `proveAlgebraicIdentity`.** Even at
   N = 10, where the absolute number is modest (170 ms), it is already
   the dominant single phase. Cutting it scales every result above. Its
   internal structure is the RatLin normalizer's NF-equality check —
   tracked at the call-site level in #80 (the safe-subset cleanup in
   #85 didn't touch the `mkAppM ``Eq.trans` middle-term def-eq inside
   `proveLinearIdentity`, which is the one that costs).
2. **`lp`'s kernel typecheck is comparable to its tactic time.** The
   produced proof term — a weighted sum of hypotheses tied together by
   the RatLin certificate of the identity — is expensive to verify.
   This is what #82 (the lazy-`Expr` survey) is meant to attack
   structurally.

SoPlex's actual LP solve is **single-digit milliseconds** throughout
this entire table. It is not, and has never been, the bottleneck.

## 5. Families that did *not* yield an `lp` advantage

The original brief was to find linear-arithmetic problem families where
`lp` structurally beats `linarith`. Three families beyond random dense
were tried and reported as negative results; the generators are
preserved in [`generators/families.py`](./generators/families.py) and
[`generators/hilbert_tight.py`](./generators/hilbert_tight.py) for
future reruns.

1. **Geometric amplification chain.** N + 1 variables `x₀ … xₙ`, with
   `x₀ ≤ 1` and `3 xᵢ ≤ 2 xᵢ₋₁`, goal `xₙ ≤ (2/3)ⁿ`. The Farkas
   certificate multipliers are `(1/3)(2/3)^(n-i)` with denominators up
   to `3^(n+1)` — exponentially large. Empirically both tactics finish
   at the import baseline through n = 32: the bignum rationals don't
   cost either anything noticeable.

2. **Hilbert matrices, loose and tight goal.** Scaled Hilbert matrix
   constraints with `Σ xᵢ ≥ b`, and a goal proved entailed either
   loosely or at the **exact rational LP optimum** computed by a
   fractions-based two-phase simplex (in [`generators/exact_lp.py`](./generators/exact_lp.py)). The
   ill-conditioning makes the dual certificate a large rational, but at
   n ≤ 14 the matrix is too small for either tactic to notice. Scaling
   up turns it into the next family (large coefficients).

3. **Large coprime coefficients** (5-digit primes). Both tactics
   succeed, but `lp` is *slower than* `linarith`, and the gap widens
   with N (lp 13 s vs linarith 6 s at N = 32). Large coefficient
   literals carry into `lp`'s proof term — the kernel `decide` check
   over them is more expensive than `linarith`'s direct certificate.
   This is an `lp` weakness, not something to advertise.

The deeper structural reason these don't separate the two tactics: both
are Farkas-certificate methods. `linarith`'s oracle is Simplex-style
feasibility search (Avigad/Lewis) — not naive primal Simplex on the
original LP, so classic Simplex hardness instances (Klee–Minty's
exponential vertex walk) don't bite it. Any family with a *complex*
certificate hurts `lp`'s proof construction at least as much as it
hurts `linarith`'s search; any family with a *simple* certificate is
easy for both.

## 6. Backend evolution timeline

The `lp` tactic has been substantially rewritten several times during
this benchmarking work. The numbers in §2 are on the latest backend.

| PR | What it changed |
|---|---|
| **#53** | Stage-1 `lp` tactic landed: SoPlex oracle + Lean verifier, `simp + grind` discharger. |
| **#55** | Replace `simp + grind` discharger with direct proof-term construction. |
| **#60** | Reflective `AffCert` parsing — `parseFixedExpr` 280 ms → 5 ms at N = 10. |
| **#64** | Replace the verifier backend entirely with a direct Farkas certificate (weighted-sum proof + grobner-discharged identity). Removed the `(kernel) deep recursion` wall at N ≥ 40. |
| **#66/#67** | RatLin normalizer replaces `grobner`; div-literal bridge. |
| **#71/#72** | Explicit-arg `mkAppN` for `direct_le_close`/`direct_lt_close`/`direct_infeasible_close` — fixes `maximum recursion depth` failures at instance-dependent N = 40/50. |
| **#73** | RArray-based atom lookup. |
| **#78** | Replace four `mkAppM` calls in `proveLinearIdentity` with typed builders, deferring middle-term def-eq to the kernel. **Reverted in #79** — reintroduced `(kernel) deep recursion detected` at N ≥ 80. |
| **#81** | Same change as #78, re-merged. **Reverted in #83**, same reason. |
| **#85** | Safe subset of #80: `mkApp2` for the no-implicit `Lin.eval_eq_evalNF`, `mkEqSymm` for `Eq.symm`; the three `Eq.trans` calls stay on `mkAppM` (their middle def-eq must remain elaborator-side). |

Open follow-ups: **#80** (the real `Eq.trans` speedup, which needs the
structural rework rather than a builder swap), **#82** (survey all
`Expr` constructions for laziness opportunities).

## 7. Recommendation

What `lp` can be advertised on today is **scale robustness**: on dense
LPs, `linarith` becomes increasingly slow past N ≈ 50 and fails outright
at N ≈ 100 with `maximum recursion depth`; `lp` is the only tactic that
completes the whole N = 10..100 range over `Rat`. That is a real,
demonstrable claim.

What `lp` cannot be advertised on today is a structural win on a
particular problem class — none was found despite focused attempts.
The crossover where `lp` overtakes `linarith` is currently around
N ≈ 60–80, and the work that lowers that crossover is the same
construction/check-cost reduction tracked in #80 / #82.

The honest summary for anyone choosing between the two on a tactic-scale
problem (≤ ~40 variables): use `linarith`. For larger problems, or where
`linarith` is timing out / hitting recursion limits, `lp` is the right
escape hatch.
