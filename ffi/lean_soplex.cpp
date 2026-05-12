/*
 * lean_soplex.cpp — thin C++ glue from the plain-C bridge ABI to SoPlex.
 *
 * Scope today is intentionally narrow: a version accessor plus a smoke
 * solve that exercises SoPlex enough to verify the build / link / runtime
 * pipeline on every CI platform. The real exact-mode API (and certificate
 * extraction) lives behind a separate set of entry points and lands in a
 * subsequent commit.
 *
 * Every entry point is `noexcept` and translates C++ exceptions into a
 * negative return code. No C++ exception is ever permitted to cross the
 * `extern "C"` boundary.
 */

#include "lean_soplex.h"

#include <cstring>
#include <exception>
#include <stdexcept>
#include <soplex.h>

using namespace soplex;

extern "C" int lean_soplex_version(void) {
  return SOPLEX_VERSION;
}

/*
 * Cross-stdlib ABI smoke check. The Windows link uses
 * `-Wl,--allow-multiple-definition` to bridge a libstdc++ / libc++
 * conflict (see lakefile.lean). The hack is only safe if libstdc++
 * definitions actually win at link time so the C++ runtime, exception
 * typeinfo, and vtable layouts match what the bridge / SoPlex objects
 * were compiled against. This entry point throws a `std::runtime_error`,
 * catches it via the `std::exception` base, and verifies the message
 * survived `.what()`. If libc++ ever wins, the catch will either miss,
 * crash, or return a corrupted message — turning the silent ABI risk
 * into a CI failure.
 *
 * Returns:
 *   0  expected message recovered
 *   1  caught but `what()` returned the wrong message
 *   2  caught only via the `...` fallback (RTTI mismatch)
 *   3  no exception escaped the `throw` (unreachable in a working build)
 */
extern "C" int lean_soplex_exception_check(void) {
  static const char *msg = "lean-soplex exception throw/catch test";
  try {
    throw std::runtime_error(msg);
  } catch (const std::exception &e) {
    if (std::strcmp(e.what(), msg) == 0) return 0;
    return 1;
  } catch (...) {
    return 2;
  }
  return 3;
}

extern "C" int lean_soplex_smoke_solve(
    int32_t numVars,
    int32_t numConstraints,
    const double *c,
    const double *b,
    int32_t a_nnz,
    const int32_t *a_rows,
    const int32_t *a_cols,
    const double *a_vals,
    double *x_out,
    double *objval_out) {
  try {
    SoPlex solver;

    // Minimisation; quiet output. Verbosity / sense control are set via
    // SoPlex's parameter system rather than positional getters.
    solver.setIntParam(SoPlex::OBJSENSE, SoPlex::OBJSENSE_MINIMIZE);
    solver.setIntParam(SoPlex::VERBOSITY, 0);

    // Columns: objective coefficient `c[j]`, bounds `[0, +inf)`, empty
    // initial column vector — sparse coefficients are supplied row-wise
    // below.
    DSVector emptyCol(0);
    for (int32_t j = 0; j < numVars; ++j) {
      solver.addColReal(LPCol(c[j], emptyCol, infinity, 0.0));
    }

    // Rows: collect sparse coefficients per row, then add as an
    // equality row `sum aᵢⱼ xⱼ = bᵢ`.
    std::vector<DSVector> rows(numConstraints);
    for (int32_t k = 0; k < a_nnz; ++k) {
      int32_t r = a_rows[k];
      int32_t j = a_cols[k];
      if (r < 0 || r >= numConstraints || j < 0 || j >= numVars) {
        return -1;
      }
      rows[r].add(j, a_vals[k]);
    }
    for (int32_t i = 0; i < numConstraints; ++i) {
      solver.addRowReal(LPRow(b[i], rows[i], b[i]));
    }

    SPxSolver::Status st = solver.optimize();
    switch (st) {
      case SPxSolver::OPTIMAL:
      case SPxSolver::OPTIMAL_UNSCALED_VIOLATIONS: {
        DVector primal(numVars);
        if (!solver.getPrimalReal(primal.get_ptr(), numVars)) {
          return -1;
        }
        for (int32_t j = 0; j < numVars; ++j) {
          x_out[j] = primal[j];
        }
        *objval_out = solver.objValueReal();
        return 0;
      }
      case SPxSolver::INFEASIBLE:
        return 1;
      case SPxSolver::UNBOUNDED:
        return 2;
      default:
        return -1;
    }
  } catch (const std::exception &) {
    return -1;
  } catch (...) {
    return -1;
  }
}
