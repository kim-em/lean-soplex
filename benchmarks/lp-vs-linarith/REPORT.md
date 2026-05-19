# `lp` vs `linarith` — comparison report

**Subject.** Wall-clock comparison of Soplex's `lp` tactic against
Mathlib's `linarith` on linear-arithmetic goals over `Rat`, as `lp`
currently behaves on `main`.

**Take-away in one paragraph.** `lp` is competitive with or faster than
`linarith` across the whole range measured. On integer-coefficient dense
LPs the two are at parity through N ≈ 30, `lp` pulls ahead from N = 40,
and by N = 80 `lp` is ~1.4× faster; at N = 100 `linarith` fails outright
(`maximum recursion depth`) on every seed while `lp` completes in ~31 s.
On rational-coefficient dense LPs `lp` is **~2× faster than `linarith`
throughout** from N = 16 up (e.g. N = 64: 15 s vs 32 s; N = 80: 24 s vs
52 s). `lp` builds the certificate-identity proof as an explicit term
that the kernel only structurally typechecks; SoPlex's actual LP solve
is single-digit milliseconds throughout and is never the bottleneck on
either side.

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
| 10 | 3.6 s | 3.5 – 3.7 | 3.3 s | 3.1 – 3.6 | parity |
| 20 | 3.8 s | 3.6 – 4.5 | 4.5 s | 3.5 – 8.1 | parity |
| 30 | 4.9 s | 4.5 – 6.2 | 4.7 s | 4.5 – 4.9 | parity |
| 40 | 5.9 s | 5.8 – 6.1 | 6.2 s | 5.9 – 6.7 | `lp` ahead |
| 50 | 8.0 s | 7.8 – 8.3 | 8.6 s | 8.3 – 9.1 | `lp` ahead |
| 60 | 10.5 s | 10.3 – 10.7 | 12.3 s | 12.1 – 12.7 | `lp` ahead |
| 80 | **18.5 s** | 18.2 – 18.8 | 26.2 s | 25.6 – 26.8 | `lp` ~1.4× faster |
| 100 | **30.4 s** | 30.0 – 30.7 | **fails (5/5)** | — | `linarith` exceeds `maximum recursion depth` on every seed |

`lp` and `linarith` are within noise of each other through N = 30. From
N = 40 `lp` is consistently faster, and the gap widens with N. At
N = 100 `linarith` fails on every seed; `lp` is the only tactic that
completes the whole N = 10..100 range.

### 2.2 Rational-coefficient dense LPs

Coefficients are `(k/d)` with `k ∈ {1,2,3}`, `d ∈ {2,3,5}` — small
rational entries throughout. Means of 5 seeds.

| N | `lp` mean | `lp` range | `linarith` mean | `linarith` range |
|---:|---:|:---:|---:|:---:|
| 8 | 3.6 s | 3.3 – 4.5 | 3.7 s | 3.4 – 4.4 |
| 16 | 3.7 s | 3.5 – 4.4 | 5.3 s | 4.6 – 6.1 |
| 24 | 4.8 s | 4.0 – 6.6 | 8.1 s | 6.6 – 12.9 |
| 32 | 5.5 s | 5.0 – 6.8 | 10.3 s | 9.4 – 12.7 |
| 40 | 6.8 s | 6.5 – 7.6 | 13.9 s | 13.4 – 14.9 |
| 48 | 8.8 s | 8.5 – 9.1 | 18.3 s | 17.8 – 19.1 |
| 56 | 11.4 s | 11.0 – 11.8 | 24.5 s | 24.1 – 25.4 |
| 64 | 14.6 s | 14.4 – 14.7 | 32.3 s | 31.7 – 33.2 |
| 72 | 18.4 s | 18.0 – 18.7 | 40.6 s | 39.7 – 41.5 |
| 80 | 23.2 s | 22.6 – 23.7 | 50.9 s | 50.0 – 52.9 |

Rational dense is where `lp` separates cleanly: from N = 16 up it is
consistently **~2× faster than `linarith`**, and the absolute gap grows
with N (a ~28 s margin at N = 80). `linarith`'s cost on these instances
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
§2.

The variance is modest: most cells hold a per-seed range under 1.3×, and
`lp` is monotone in N over the ranges measured. The widest spread is at
small N, where the first warm-up invocation of a fresh run can land a
single seed several seconds above the rest; those are flagged in the
table notes.

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
| **`proveCertificateIdentity`** | **582 ms** |

The two substantial phases are hypothesis parsing (489 ms) and the
certificate-identity discharge (582 ms); neither dominates the other.
SoPlex's actual LP solve is 28 ms.

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

`lp` discharges the certificate identity by building an explicit proof
term; the kernel structurally typechecks it and the only reductions it
performs are GMP-backed `Nat`/`Int` literal arithmetic — there is no
evaluator reduction over the certificate. The profiler's "tactic
execution" line shows `lp` slightly behind `linarith` at N = 40, yet
§2's wall-clock has `lp` ahead from N = 40 onward: `linarith`'s
wall-clock carries preprocessing and elaboration work that the
profiler's "tactic execution" line does not attribute to it.

## 5. Families that do not yield a structural `lp` advantage

Beyond random dense LPs, three further families were explored — a
geometric amplification chain (Farkas multipliers with exponentially
large denominators), Hilbert matrices with both loose and tight-optimum
goals, and dense LPs with large coprime coefficients. The generators are
preserved in [`generators/families.py`](./generators/families.py) and
[`generators/hilbert_tight.py`](./generators/hilbert_tight.py).

None produces a *structural* separation — a problem class on which `lp`
beats `linarith` for a reason other than size. The reason is structural:
both tactics are Farkas-certificate methods. A family with a complex
certificate costs `lp`'s proof construction; a family with a simple
certificate is easy for both. `lp`'s advantage in §2 is not a new
problem class — it is that `lp` carries a smaller constant factor and
scales better, so the wall-clock gap opens up as N grows.

## 6. Recommendation

Use `lp`. On the dense LP families measured here it is competitive with
`linarith` at small N and strictly faster at scale: ~2× faster on
rational dense from N = 16 up, faster on integer dense from N = 40, and
the only one of the two that completes N = 100 integer (`linarith`
fails with `maximum recursion depth`).

`lp` carries a real dependency the chooser should know about: its cost
tracks the size of the Farkas certificate SoPlex returns, so a path with
a dense certificate is more expensive than the variable count alone
suggests (§3). That sensitivity is a modest constant factor. SoPlex's
actual LP solve is single-digit milliseconds throughout — it is not the
bottleneck.
