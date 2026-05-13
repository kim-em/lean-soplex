# SoPlex rational accessors → canonical `DualBundle`

Pinned SoPlex release: **v8.0.2** (`SOPLEX_VERSION = 802`, April 2026).

This document records the sign and meaning of each SoPlex rational
accessor used by the bridge, and the exact translation `ffi/lean_soplex_bridge.cpp`
applies to land them in the canonical lower/upper-split `DualBundle`
that `LeanSoplex.Verify.checkOptimal`, `checkInfeasible`, and
`checkUnbounded` consume.

The translation is *untrusted*: the verification layer catches
mistakes here as non-verifying certificates. The exhaustive
row-sense × column-status × min/max golden tests in
`AccessorGoldens.lean` pin down the conventions below by running one
tiny LP per cell and asserting the resulting `DualBundle` exactly. A
SoPlex bump that changes any convention will break those goldens
before it can mis-translate a real certificate.

## Conventions and notation

All accessors below act on the LP `solveExact` sends to SoPlex —
i.e. the **minimisation** form produced by
`LeanSoplex.Verify.canonicalize`. For `Options.sense := .maximize`,
`canonicalize` negates `c` before the LP reaches the C++ bridge, so
SoPlex always sees a minimisation LP and every accessor convention
below is stated relative to that minimisation form. The
user-facing `Solution.objective` is then flipped back into the
caller's sense by `mapObjectiveForSense`.

The canonical LP is

```
  minimise   c · x + objOffset
  subject to lo_rᵢ ≤ (Ax)ᵢ ≤ hi_rᵢ      (rowBounds[i] = (lo_r, hi_r))
             lo_cⱼ ≤ xⱼ    ≤ hi_cⱼ      (colBounds[j] = (lo_c, hi_c))
```

with `none` denoting `±∞`. The canonical dual (`DualBundle`) stores
the four non-negative multiplier arrays:

```
  rowLower[i]   for   lo_rᵢ ≤ (Ax)ᵢ
  rowUpper[i]   for           (Ax)ᵢ ≤ hi_rᵢ
  colLower[j]   for   lo_cⱼ ≤ xⱼ
  colUpper[j]   for           xⱼ ≤ hi_cⱼ
```

The signed row dual is `y = rowLower − rowUpper`; the signed reduced
cost is `z = colLower − colUpper`.

## Accessor → bridge translation summary

| SoPlex accessor               | Length          | What SoPlex returns (sign convention)               | Bridge translation |
|-------------------------------|-----------------|------------------------------------------------------|--------------------|
| `getPrimalRational`           | `numVars`       | Optimal primal `x` (or feasible base point if unbounded). Signed values, satisfying all bounds. | Stored verbatim into `Solution.certificate.primal`. |
| `getPrimalRayRational`        | `numVars`       | A recession ray `r` along which the objective improves (decreases for min). | Stored verbatim into `Solution.certificate.ray`. |
| `getDualRational`             | `numConstraints`| Signed row dual `y`. `y > 0` ⇒ row lower bound active; `y < 0` ⇒ row upper bound active; `y = 0` for free rows or rows whose multiplier is zero at optimum. | Split: `rowLower = max(y, 0)`, `rowUpper = max(−y, 0)` (`split_pos`). |
| `getRedCostRational`          | `numVars`       | Signed reduced cost `z = c − Aᵀy` (post-canonicalisation). `z > 0` ⇒ column at lower bound; `z < 0` ⇒ column at upper bound; `z = 0` for basic / free columns. | Split: `colLower = max(z, 0)`, `colUpper = max(−z, 0)` (`split_pos`). |
| `getDualFarkasRational`       | `numConstraints`| Signed Farkas multiplier `y`. SoPlex's sign convention here can flip depending on which side certifies infeasibility; the bridge canonicalises so that the bound combination `Σᵢ lo_rᵢ·y⁺ − hi_rᵢ·y⁻ + Σⱼ lo_cⱼ·z⁺ − hi_cⱼ·z⁻` is **strictly positive** (the Farkas certificate the verifier wants). | Compute `−Aᵀy` (the implied column-side multiplier), check `bound_combination_sign`; if negative, negate both `y` and `Aᵀy` first. Then `split_pos` into the four arrays exactly as for the optimal case. |

## Per-cell sign behaviour

The 17 cells of the row-sense × column-status matrix below are each
exercised by `AccessorGoldens.lean` in both senses. The "signed
SoPlex output" column shows the values `getDualRational` /
`getRedCostRational` return for the canonical (min) LP; the
"`DualBundle` after split" column is what
`Solution.certificate.dual` reports. The max-sense run uses the same
LP but with `c` negated upstream by the user — after
`canonicalize`, SoPlex sees the same min LP, so the canonical dual
values are identical.

Each cell below lists, for the canonical (post-`canonicalize`) min
LP: the example we feed SoPlex, the optimal `x`, the signed `y`
that `getDualRational` returns for the (one) row, the signed `z`
that `getRedCostRational` returns for the (one) column, and the
full `DualBundle` after `split_pos` (in
`rowLower / rowUpper / colLower / colUpper` order). For the
free-free degenerate case `x` is non-unique and we only pin the
dual; for every other cell we pin the primal too.

### Free row (`rowBounds = (none, none)`)

The row constraint is vacuous; SoPlex returns `y = 0` for that row,
which the bridge splits as `rowLower[i] = rowUpper[i] = 0`. The
column status then drives the reduced cost.

| Column status        | Example                        | Optimal `x` | Signed `y` | Signed `z` | `DualBundle (rL / rU / cL / cU)` |
|----------------------|--------------------------------|-------------|------------|------------|----------------------------------|
| free                 | `c = 0`, no col bounds         | (any; `0`)  | `0`        | `0`        | `[0] / [0] / [0] / [0]`           |
| fixed (`x = 2`)      | `c = 1`                         | `2`         | `0`        | `+1`       | `[0] / [0] / [1] / [0]`           |
| lower-only (`x ≥ 2`) | `c = 1`                         | `2`         | `0`        | `+1`       | `[0] / [0] / [1] / [0]`           |
| upper-only (`x ≤ 3`) | `c = −1`                       | `3`         | `0`        | `−1`       | `[0] / [0] / [0] / [1]`           |
| boxed (`1 ≤ x ≤ 5`)  | `c = 1`                         | `1`         | `0`        | `+1`       | `[0] / [0] / [1] / [0]`           |

### Equality row (`rowBounds = (some b, some b)`)

The row binds at `b` (both sides). The signed row dual `y` carries
the full shadow price; SoPlex picks `sign(y) = sign(c)` for the
single-variable / single-row case below, so the bridge sends the
whole multiplier into `rowLower` when `c > 0`. The column bound is
slack (`x = 2` is interior), so `z = 0` in every row.

| Column status        | Example (`row: x = 2`)         | Optimal `x` | Signed `y` | Signed `z` | `DualBundle (rL / rU / cL / cU)` |
|----------------------|--------------------------------|-------------|------------|------------|----------------------------------|
| lower-only (`x ≥ 0`) | `c = 1`                         | `2`         | `+1`       | `0`        | `[1] / [0] / [0] / [0]`           |
| upper-only (`x ≤ 5`) | `c = 1`                         | `2`         | `+1`       | `0`        | `[1] / [0] / [0] / [0]`           |
| boxed (`0 ≤ x ≤ 5`)  | `c = 1`                         | `2`         | `+1`       | `0`        | `[1] / [0] / [0] / [0]`           |

### Lower-only row (`rowBounds = (some lo, none)`)

The lower row bound binds at the minimisation optimum; SoPlex
returns `y > 0`, which the bridge splits into `rowLower`. The
column bound is slack, so `z = 0`.

| Column status        | Example (`row: x ≥ 1`)         | Optimal `x` | Signed `y` | Signed `z` | `DualBundle (rL / rU / cL / cU)` |
|----------------------|--------------------------------|-------------|------------|------------|----------------------------------|
| lower-only (`x ≥ 0`) | `c = 1`                         | `1`         | `+1`       | `0`        | `[1] / [0] / [0] / [0]`           |
| upper-only (`x ≤ 5`) | `c = 1`                         | `1`         | `+1`       | `0`        | `[1] / [0] / [0] / [0]`           |
| boxed (`0 ≤ x ≤ 5`)  | `c = 1`                         | `1`         | `+1`       | `0`        | `[1] / [0] / [0] / [0]`           |

### Upper-only row (`rowBounds = (none, some hi)`)

The upper row bound binds; SoPlex returns `y < 0`, which the bridge
splits into `rowUpper`.

| Column status        | Example (`row: x ≤ 3`)         | Optimal `x` | Signed `y` | Signed `z` | `DualBundle (rL / rU / cL / cU)` |
|----------------------|--------------------------------|-------------|------------|------------|----------------------------------|
| lower-only (`x ≥ 0`) | `c = −1`                       | `3`         | `−1`       | `0`        | `[0] / [1] / [0] / [0]`           |
| upper-only (`x ≤ 5`) | `c = −1`                       | `3`         | `−1`       | `0`        | `[0] / [1] / [0] / [0]`           |
| boxed (`0 ≤ x ≤ 5`)  | `c = −1`                       | `3`         | `−1`       | `0`        | `[0] / [1] / [0] / [0]`           |

### Ranged row (`rowBounds = (some lo, some hi)` with `lo < hi`)

Both row bounds finite; only the binding side gets a nonzero
multiplier. The cell-matrix examples pick `c > 0` to bind the lower
row bound. The supplemental case in `AccessorGoldens.lean`
(`C_ranged_upper_binding`, `c = -1`, same ranged row, lower-only col)
also pins the upper-side-binding case, which mirrors the upper-only
table above.

| Column status        | Example (`row: 1 ≤ x ≤ 3`)     | Optimal `x` | Signed `y` | Signed `z` | `DualBundle (rL / rU / cL / cU)` |
|----------------------|--------------------------------|-------------|------------|------------|----------------------------------|
| lower-only (`x ≥ 0`) | `c = 1` (lower binds)           | `1`         | `+1`       | `0`        | `[1] / [0] / [0] / [0]`           |
| lower-only (`x ≥ 0`) | `c = -1` (upper binds) †        | `3`         | `−1`       | `0`        | `[0] / [1] / [0] / [0]`           |
| upper-only (`x ≤ 5`) | `c = 1`                         | `1`         | `+1`       | `0`        | `[1] / [0] / [0] / [0]`           |
| boxed (`0 ≤ x ≤ 5`)  | `c = 1`                         | `1`         | `+1`       | `0`        | `[1] / [0] / [0] / [0]`           |

† Supplemental `C_ranged_upper_binding` case; the in-matrix
upper-bound-binding behaviour is otherwise covered by the upper-only
row table above.

### Non-unit `A`

The matrix cells use `A = [[1]]`, so stationarity reduces to
`c = y + z`. The supplemental cases pin the bridge for non-unit and
sign-flipped matrix entries:

| Case                                 | LP                                                          | Signed `y` | Signed `z` | `DualBundle (rL / rU / cL / cU)` |
|--------------------------------------|-------------------------------------------------------------|------------|------------|----------------------------------|
| `C_nonunit_pos` (`A = +2`)            | `min x s.t. 2x ≥ 4, x ≥ 0`                                  | `+1/2`     | `0`        | `[1/2] / [0] / [0] / [0]`         |
| `C_nonunit_neg` (`A = -1`)            | `min x s.t. -x ≤ -2, x ≥ 0`                                 | `−1`       | `0`        | `[0] / [1] / [0] / [0]`           |

### Multi-row dual mix

Two equality rows whose duals genuinely have opposite signs: pins
that `split_pos` operates row-wise rather than collapsing across
the dual vector.

| Case            | LP                                                                             | Signed `y` | `DualBundle.rowLower / rowUpper` |
|-----------------|--------------------------------------------------------------------------------|------------|----------------------------------|
| `C_two_row_dual`| `min x + 2y s.t. x + y = 3, x = 1, x ≥ 0, y ≥ 0`                                | `(2, −1)`  | `[2, 0] / [0, 1]`                  |

## Sense (`.minimize` vs `.maximize`)

`Options.sense := .maximize` is implemented entirely above the
bridge by `canonicalize`, which negates `c` (and `objOffset`)
before the LP is sent to SoPlex. Concretely:

* The C++ bridge always calls `setIntParam(OBJSENSE, OBJSENSE_MINIMIZE)`.
* For the same `Problem` value, `solveExact` with `sense = .maximize`
  sends `−c` and reports `−objective`, but the LP SoPlex actually
  solves — and therefore the `DualBundle` SoPlex returns — is the
  same as solving the negated user-facing LP with `sense = .minimize`.
* `AccessorGoldens.lean` exploits this by running each canonical LP
  twice: once with the canonical `c` and `.minimize`, once with the
  negated `c` and `.maximize`. Both runs assert the **same**
  `expectedDual`; only the user-facing `objective` flips sign.

This is exactly what `LeanSoplex.Verify` expects: `checkOptimal` is
always invoked against `canonicalize sense p`, never against the
raw user-facing `Problem`.

By design the max-sense run does **not** exercise an
independent SoPlex max-sense code path — `canonicalize` collapses
both senses to the same LP before the FFI boundary. The max-sense
column therefore checks the bridge's handling of
`mapObjectiveForSense` (the user-facing-objective sign flip) and
`canonicalize`'s sign discipline, not SoPlex's
`OBJSENSE_MAXIMIZE` parameter (which the bridge intentionally
never sets). `SolveExactTests.tMaximize` covers the
end-to-end max-sense user-API path with an asymmetric LP.

## Unbounded and infeasible cases

`getPrimalRayRational` and `getDualFarkasRational` are exercised by
`SolveExactTests.lean` rather than by this matrix (the
row-sense × column-status pattern only makes sense for an LP whose
optimum exists). Bridge behaviour for those accessors:

| Accessor                  | Test fixture                           | LP                                                  | What the bridge does |
|---------------------------|----------------------------------------|------------------------------------------------------|----------------------|
| `getPrimalRayRational`    | `SolveExactTests.tUnbounded`           | `min -x s.t. x ≥ 0` (no rows; col lower bound only). | Stored verbatim into `Solution.certificate.ray`. The pure-Lean `isRecessionRay` checks the shape; `dot c r < 0` confirms it improves the objective in canonical min sense. |
| `getDualFarkasRational`   | `SolveExactTests.tInfeasibleRowsOnly`  | `min 0 s.t. x ≥ 1, x ≤ 0` (two contradictory rows; free col). | Compute `−Aᵀy` for the implied column-side multiplier, call `bound_combination_sign` to check the canonical bound combination, *negate both `y` and `−Aᵀy` if it came out negative*, then `split_pos` into the four `DualBundle` arrays. The verifier's `boundCombinationPos` then sees a strictly-positive combination. |
| `getDualFarkasRational`   | `SolveExactTests.tInfeasibleRowAndBounds` | `min 0 s.t. x ≥ 2, 0 ≤ x ≤ 1` (rows + bound contradiction). | Same translation; in this case the column-side multipliers `−Aᵀy` carry the bound contribution. |

Both Farkas examples confirm:

* Homogeneous stationarity `Aᵀ(yL − yU) + (zL − zU) = 0` holds
  (`isFarkasFeasible`).
* Strict positivity of the bound combination
  `Σᵢ lo_rᵢ·yLᵢ − hi_rᵢ·yUᵢ + Σⱼ lo_cⱼ·zLⱼ − hi_cⱼ·zUⱼ > 0`
  (`boundCombinationPos`), regardless of which side of SoPlex's
  signed Farkas vector certified infeasibility.

## When this document goes stale

Whenever the pinned SoPlex tag in `lakefile.lean` (or the bridge's
parameter setup in `ffi/lean_soplex_bridge.cpp`) changes:

1. Re-run `lake exe accessor-goldens` against the new SoPlex.
2. If any case fails, update the bridge until the goldens pass.
3. Update the example tables above to reflect any new sign
   conventions, and refresh the pinned-release line at the top of
   this document.
