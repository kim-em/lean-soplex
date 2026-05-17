# `lp` Expr Construction Inventory

This inventory covers the proof-facing `Expr` construction sites in
`Soplex/Tactic/LP.lean` and `Soplex/Tactic/RatLin/*.lean`, with emphasis
on whether a construction is always consumed on a successful `lp` path.

## `Soplex/Tactic/LP.lean`

| Site | Need | Cost estimate | Action |
| --- | --- | --- | --- |
| `collectHypProof`: `And.left` / `And.right` projections | Needed to inspect conjunctive hypotheses. | One projection per conjunct edge; small and proportional to parsed context shape. | Left eager. |
| `collectHypProof`: row `lhs - rhs` terms | Needed only for rows whose dual/Farkas multiplier is nonzero. Rows ignored by the certificate do not need the term. | One `HSub.hSub` elaboration per parsed row; noticeable on dense contexts with many unused rows. | Made lazy as `Row.term : MetaM Expr`. |
| `collectHypProof`: row proofs (`rat_sub_nonpos_of_le`, `rat_sub_nonpos_of_eq`, `mkEqSymm`) | Needed only for rows whose multiplier is nonzero. | One closer application per used row; equality's reverse row additionally needs `mkEqSymm`. | Already lazy as `Row.proof : MetaM Expr`; retained. |
| `solveAtomic`: parsed goal-side `LinExpr`s from `parseAtomic?` | Needed to discover goal variables before calling `proveEntailed`; equality goals reuse the same parse to seed both directions. | Numeric parse plus reducible whnf; no proof-term construction. | Left eager. |
| `proveEntailed`: objective `rhs - lhs` `LinExpr` | Needed to detect the closed-goal short-circuit and to build the LP objective. | Numeric parse; no proof-term construction. | Left eager. |
| `proveEntailed`: dense row arrays and row constants | Needed only if the closed-goal short-circuit does not fire and SoPlex is called. | Numeric, not `Expr`, but can dominate large closed goals by walking all rows. | Moved after the short-circuit. |
| `assembleLeProof`: residual sign proof, `rhs - lhs`, weighted sum, identity, final closer | Needed only on the optimal/closed-goal path after numerical checks pass. | Proportional to nonzero certificate rows plus RatLin identity size. | Already branch-local. |
| `proveEntailed` infeasible branch: Farkas residual, weighted sum, identity, `False.elim` goal type | Needed only when SoPlex reports infeasible. | Proportional to nonzero Farkas rows plus identity size. | Already branch-local; row term forcing now lazy. |
| `proveEntailed` unbounded branch: diagnostic strings | Needed only for the unbounded error. | String-only, no proof `Expr`. | Left branch-local. |
| `solveGoal`: `And.intro` and child metavariables | Needed only for conjunctive goals. | Small per goal split. | Left branch-local. |

## `Soplex/Tactic/RatLin/Tactic.lean`

| Site | Need | Cost estimate | Action |
| --- | --- | --- | --- |
| `bridgeRatDivLits`: rewritten expression and bridge proof | Needed when an identity contains primitive `(n : Rat) / d` literals, because emitted `Lin.eval` must be definitionally aligned with `Q.toRat`. | Proportional to the expression nodes containing bridged literals. | Left eager inside the identity discharger; the whole discharger is already only called from proof-producing branches. |
| `parseExpr`: `LinM` metaprogram AST | Needed before proof emission to check both sides normalise to the same `NF`. | Numeric/metaprogram structure, not Lean proof `Expr`. | Left eager. |
| `mkLinExpr` / `mkQExpr` | Needed only after the NF equality check succeeds. | Proportional to the final identity AST; `mkQExpr` builds denominator side-condition proofs for literals. | Already after the check. |
| `mkRho` | Needed for every emitted RatLin proof. | One emitted atom table; logarithmic lookup in kernel reduction. | Left eager in the proof-producing path. |
| `Lin.eval_eq_evalNF`, `mkEqSymm`, `mkEqTrans`, bridge transports | Needed for every successful identity proof, with bridge transports only when a bridge exists. | Constant number of equality combinators plus optional bridge chain. | Already branch-local. |

The main systematic laziness invariant after this pass is that parsed
rows carry only numeric data eagerly. Lean proof-side row artefacts are
forced at certificate assembly time and only for rows with nonzero
multipliers.
