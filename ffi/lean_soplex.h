#ifndef LEAN_SOPLEX_H
#define LEAN_SOPLEX_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * Compile-time SoPlex version as a single integer.
 *
 * Equal to the `SOPLEX_VERSION` macro baked into the SoPlex headers used
 * at compile time. For SoPlex `vM.m.p` we have version = `M*100 + m*10 + p`,
 * so e.g. v8.0.2 → 802.
 */
int lean_soplex_version(void);

/*
 * Cross-stdlib ABI smoke check. Throws `std::runtime_error`, catches it
 * via the `std::exception` base, validates `what()`. Returns 0 on
 * success. See implementation in `lean_soplex.cpp` for full
 * documentation; exists primarily to validate the Windows
 * `--allow-multiple-definition` link workaround.
 */
int lean_soplex_exception_check(void);

/*
 * Smoke-test solve.
 *
 * Builds the LP
 *
 *     minimize     c[0]*x[0] + ... + c[numVars-1]*x[numVars-1]
 *     subject to   sum_j a_vals[a_offsets[i]..a_offsets[i+1]] * x[a_cols[..]] = b[i]
 *                  for i = 0..numConstraints-1
 *                  0 <= x <= +inf
 *
 * inside SoPlex, solves it in the default (floating-point) mode, and writes
 * the primal solution into `x_out` (length `numVars`).
 *
 * Returns one of:
 *   0  optimal (`x_out` and `*objval_out` populated)
 *   1  infeasible
 *   2  unbounded
 *  -1  any internal SoPlex error or unhandled status
 *
 * This is intentionally narrow: just enough surface area to exercise the
 * full FFI / link / runtime pipeline end-to-end. The real API lives behind
 * `solveExact` / `solveFloat` and goes in later.
 */
int lean_soplex_smoke_solve(
    int32_t numVars,
    int32_t numConstraints,
    const double *c,
    const double *b,
    int32_t a_nnz,
    const int32_t *a_rows,
    const int32_t *a_cols,
    const double *a_vals,
    double *x_out,
    double *objval_out);

#ifdef __cplusplus
}
#endif

#endif
