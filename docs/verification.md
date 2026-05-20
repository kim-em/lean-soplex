# Verification and Trust Model

Soplex treats SoPlex as an unverified mathematical oracle. SoPlex may
find exact certificates, but every certificate must be checked by the
pure-Lean verifier before Soplex exposes a proof-carrying result.
Incorrect certificates, including certificates affected by solver bugs
or sign-convention translation mistakes, are rejected and surfaced as
`Verified.unchecked`.

The native C++ FFI remains part of the runtime trusted computing base.
It is trusted to run safely in-process, preserve memory safety and ABI
correctness, and faithfully marshal Lean-side `Problem` and certificate
data. The Lean checker protects the mathematical proof boundary; it
does not make arbitrary native memory-safety or ABI failures harmless.

## Verified Solve Pipeline

`solveVerified` validates and normalizes the Lean-side `Problem`,
forces `Options.presolve := false`, runs exact-mode SoPlex, and checks
the returned certificate against the normalized Lean-side problem. The
checker never validates certificates against data round-tripped through
C++.

`Verified` is indexed by the normalized problem and the objective
sense. Its proof-carrying constructors are:

* `.optimal x h`, where `h` proves feasibility and optimality;
* `.infeasible h`, where `h` proves that the problem is infeasible;
* `.unbounded x r h`, where `h` proves an unbounded ray from a feasible
  point.

The `.unchecked status` constructor covers undecided solver statuses
and failed certificate checks. It carries no Lean proof of optimality,
infeasibility, or unboundedness.

## Presolve

Direct `solveExact` calls may use SoPlex presolve. The verified path
forces presolve off because the returned certificate is checked against
the original normalized Lean-side problem. Reconstructing certificates
for the original problem from presolve output is intentionally outside
the current verified pipeline.

## Dual Multipliers

Dual multipliers are stored as a nonnegative lower/upper split per row
and column. This representation is more explicit than a signed dual
vector and handles ranged rows and boxed columns uniformly.

For infeasibility and optimality certificates, the checker combines the
selected lower-bound and upper-bound multipliers with the normalized
problem data and verifies the resulting rational identities and
inequalities in Lean.

## Maximization

SoPlex certificate checking is canonicalized internally through a
minimization view. Maximization reduces to minimization by negating the
objective during checking.

This canonicalization is internal: user-facing objectives and
witnesses remain in the caller's original sense. In particular,
reported objective values and `objOffset` are interpreted using the
same objective sense the caller requested.

## Denominator Budgets

The denominator budget limits certificate rational size so that
pathological certificates do not force unbounded checker work. It caps
the combined numerator plus denominator bit length of every certificate
rational.

The default budget is `some 10000`. If any certificate rational exceeds
the budget, the verified path returns
`Verified.unchecked .budgetExceeded`. Pass `none` to disable the budget.

## Related Code

The high-level API and driver live in [`Soplex/Basic.lean`](../Soplex/Basic.lean)
and [`Soplex/Verify/Driver.lean`](../Soplex/Verify/Driver.lean). The
certificate types, validation code, soundness lemmas, and budget checks
are under [`Soplex/Verify/`](../Soplex/Verify/).
