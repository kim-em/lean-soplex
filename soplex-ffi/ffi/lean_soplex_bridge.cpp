/*
 * Lean-callable bridge: unpacks Lean ByteArray / FloatArray inputs, calls
 * into `lean_soplex.cpp`, and packages the result as a Lean ADT.
 *
 * Pattern matches `lean-csdp` exactly: integer arrays are passed as
 * ByteArrays of int32 entries; floating-point arrays as FloatArrays.
 *
 * Compiled as C++ because Lean's runtime headers and SoPlex's headers both
 * need a C++ translation unit somewhere; making the bridge itself C++
 * keeps the entire FFI in one language.
 */

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <exception>
#include <fstream>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <vector>

#include <lean/lean.h>
#include <gmp.h>
#ifndef NDEBUG
#define NDEBUG
#endif
#include <soplex.h>

#include "lean_soplex.h"

using namespace soplex;

/*
 * Same glibc-compatibility shim as in `lean-csdp`: Lean's bundled clang on
 * Linux still references `__libc_csu_init` / `__libc_csu_fini` from the
 * CRT, but glibc 2.34+ removed them. Provide weak fallbacks that walk
 * `.init_array` / `.fini_array` so global constructors (and SoPlex has
 * many) run correctly.
 */
#if defined(__linux__) && defined(__GLIBC__)
extern "C" {
typedef void (*csu_init_fn)(int, char **, char **);
typedef void (*csu_fini_fn)(void);

extern csu_init_fn __init_array_start[] __attribute__((weak, visibility("hidden")));
extern csu_init_fn __init_array_end[]   __attribute__((weak, visibility("hidden")));
extern csu_fini_fn __fini_array_start[] __attribute__((weak, visibility("hidden")));
extern csu_fini_fn __fini_array_end[]   __attribute__((weak, visibility("hidden")));

__attribute__((weak)) void __libc_csu_init(int argc, char **argv, char **envp) {
  for (size_t i = 0; &__init_array_start[i] != __init_array_end; ++i) {
    __init_array_start[i](argc, argv, envp);
  }
}

__attribute__((weak)) void __libc_csu_fini(void) {
  size_t i = (size_t)(__fini_array_end - __fini_array_start);
  while (i-- > 0) __fini_array_start[i]();
}
} // extern "C"
#endif

static inline const int32_t *byte_array_as_i32(b_lean_obj_arg arr) {
  return reinterpret_cast<const int32_t *>(lean_sarray_cptr(arr));
}

static inline const double *float_array_const_ptr(b_lean_obj_arg arr) {
  return lean_float_array_cptr(arr);
}

static inline uint8_t byte_array_u8(b_lean_obj_arg arr, size_t i) {
  return lean_sarray_cptr(arr)[i];
}

static inline std::string lean_string_at(b_lean_obj_arg arr, size_t i) {
  lean_object *s = lean_array_get_core(arr, i);
  return std::string(lean_string_cstr(s));
}

/*
 * RAII redirection of SoPlex's `spxout` to an in-memory buffer.
 *
 * When `enabled` is true, the constructor allocates an `ostringstream`
 * and points every verbosity level's stream at it; the destructor
 * restores the original stream pointers. When `enabled` is false the
 * helper is a complete no-op: no allocation, no setStream calls, and
 * `str()` returns an empty string.
 *
 * Designed for use around any SoPlex call site that wants to capture
 * solver output. The reference to `SoPlex` is non-owning; the solver
 * must outlive this object. `SPxOut` stores raw, non-owning
 * `std::ostream*` pointers, so the saved streams (typically the
 * process-default `cout`/`cerr`) must outlive both the solver and
 * this capture — true by default; only a custom caller-installed
 * stream could violate it.
 */
class LogCapture {
 public:
  LogCapture(soplex::SoPlex &solver, bool enabled)
      : solver_(solver), enabled_(enabled) {
    if (!enabled_) return;
    oss_.reset(new std::ostringstream());
    for (int v = 0; v < kNumVerbLevels; ++v) {
      auto verb = static_cast<soplex::SPxOut::Verbosity>(v);
      saved_[v] = &solver_.spxout.getStream(verb);
      solver_.spxout.setStream(verb, *oss_);
    }
  }
  // Vendored `SPxOut::setStream` is non-throwing (a single pointer
  // assignment), so restoration is safe to run during stack unwinding.
  ~LogCapture() noexcept {
    if (!enabled_) return;
    for (int v = 0; v < kNumVerbLevels; ++v) {
      auto verb = static_cast<soplex::SPxOut::Verbosity>(v);
      solver_.spxout.setStream(verb, *saved_[v]);
    }
  }
  LogCapture(const LogCapture &) = delete;
  LogCapture &operator=(const LogCapture &) = delete;

  std::string str() const {
    return enabled_ ? oss_->str() : std::string{};
  }

 private:
  // SoPlex's `Verbosity` enum is documented as a contiguous range
  // `VERB_ERROR == 0` .. `VERB_INFO3 == 5`; see `soplex/spxout.h`.
  static_assert(static_cast<int>(soplex::SPxOut::VERB_ERROR) == 0,
                "SPxOut::VERB_ERROR must be 0");
  static_assert(static_cast<int>(soplex::SPxOut::VERB_INFO3) == 5,
                "SPxOut::VERB_INFO3 must be 5 (six contiguous verbosity levels)");
  static constexpr int kNumVerbLevels = static_cast<int>(soplex::SPxOut::VERB_INFO3) + 1;

  soplex::SoPlex &solver_;
  bool enabled_;
  std::unique_ptr<std::ostringstream> oss_;
  std::ostream *saved_[kNumVerbLevels] = {};
};

class Mpq {
 public:
  mpq_t q;

  Mpq() { mpq_init(q); }
  explicit Mpq(const std::string &s) {
    mpq_init(q);
    if (mpq_set_str(q, s.c_str(), 10) != 0) {
      throw std::runtime_error("invalid rational string: " + s);
    }
    mpq_canonicalize(q);
  }
  Mpq(const Mpq &) = delete;
  Mpq &operator=(const Mpq &) = delete;
  Mpq(Mpq &&other) noexcept {
    mpq_init(q);
    mpq_swap(q, other.q);
  }
  Mpq &operator=(Mpq &&other) noexcept {
    if (this != &other) mpq_swap(q, other.q);
    return *this;
  }
  ~Mpq() { mpq_clear(q); }
};

static lean_object *mk_rat_from_mpq(const mpq_t q) {
  mpq_t z;
  mpq_init(z);
  mpq_set(z, q);
  mpq_canonicalize(z);
  char *num = mpz_get_str(nullptr, 10, mpq_numref(z));
  char *den = mpz_get_str(nullptr, 10, mpq_denref(z));
  if (num == nullptr || den == nullptr) {
    mpq_clear(z);
    throw std::runtime_error("mpz_get_str failed");
  }
  lean_object *r = lean_alloc_ctor(0, 4, 0);
  lean_ctor_set(r, 0, lean_cstr_to_int(num));
  lean_ctor_set(r, 1, lean_cstr_to_nat(den));
  lean_ctor_set(r, 2, lean_box(0));
  lean_ctor_set(r, 3, lean_box(0));
  void (*freefunc)(void *, size_t);
  mp_get_memory_functions(nullptr, nullptr, &freefunc);
  freefunc(num, std::strlen(num) + 1);
  freefunc(den, std::strlen(den) + 1);
  mpq_clear(z);
  return r;
}

static lean_object *mk_rat_from_string(const std::string &s) {
  Mpq q(s);
  return mk_rat_from_mpq(q.q);
}

/*
 * Build a Lean `Rat` from an IEEE-754 double via `mpq_set_d`. The result
 * is the *exact* rational represented by the double's binary fraction,
 * e.g. `0.1` becomes `7205759403792794 / 2^56`, not `1/10`. Used by
 * `lean_soplex_solve_float` to surface SoPlex's `Real` primal values
 * losslessly as rationals — never as a verifier-grade certificate.
 */
static lean_object *mk_rat_from_double(double d) {
  Mpq q;
  mpq_set_d(q.q, d);
  mpq_canonicalize(q.q);
  return mk_rat_from_mpq(q.q);
}

/*
 * Parse a Lean-side decimal-string `Rat` to a `double`. Used by the
 * float-mode bridge to feed `addColReal` / `addRowReal`.
 */
static double parse_rat_to_double(const std::string &s) {
  Mpq q(s);
  return mpq_get_d(q.q);
}

struct FlatProblemInput {
  int numVars;
  int numConstraints;
  size_t nnz;
  const int32_t *aRows;
  const int32_t *aCols;
  b_lean_obj_arg c;
  b_lean_obj_arg aVals;
  b_lean_obj_arg rowLoMask;
  b_lean_obj_arg rowLo;
  b_lean_obj_arg rowHiMask;
  b_lean_obj_arg rowHi;
  b_lean_obj_arg colLoMask;
  b_lean_obj_arg colLo;
  b_lean_obj_arg colHiMask;
  b_lean_obj_arg colHi;
};

static FlatProblemInput flat_problem_input(
    uint32_t numVars_u, uint32_t numConstraints_u,
    b_lean_obj_arg c_arr,
    b_lean_obj_arg a_rows_arr, b_lean_obj_arg a_cols_arr, b_lean_obj_arg a_vals_arr,
    b_lean_obj_arg rowLoMask, b_lean_obj_arg rowLo,
    b_lean_obj_arg rowHiMask, b_lean_obj_arg rowHi,
    b_lean_obj_arg colLoMask, b_lean_obj_arg colLo,
    b_lean_obj_arg colHiMask, b_lean_obj_arg colHi) {
  return FlatProblemInput{
      static_cast<int>(numVars_u),
      static_cast<int>(numConstraints_u),
      lean_sarray_size(a_rows_arr) / sizeof(int32_t),
      byte_array_as_i32(a_rows_arr),
      byte_array_as_i32(a_cols_arr),
      c_arr,
      a_vals_arr,
      rowLoMask,
      rowLo,
      rowHiMask,
      rowHi,
      colLoMask,
      colLo,
      colHiMask,
      colHi};
}

struct RationalProblemData {
  std::vector<Mpq> cVals;
  std::vector<Mpq> aVals;
  std::vector<std::vector<int>> rowIdx;
  std::vector<std::vector<size_t>> rowValIdx;
};

static RationalProblemData parse_rational_problem_data(const FlatProblemInput &in) {
  RationalProblemData data;
  data.cVals.reserve(in.numVars);
  for (int j = 0; j < in.numVars; ++j) data.cVals.emplace_back(lean_string_at(in.c, j));

  data.aVals.reserve(in.nnz);
  for (size_t k = 0; k < in.nnz; ++k) data.aVals.emplace_back(lean_string_at(in.aVals, k));

  data.rowIdx.resize(in.numConstraints);
  data.rowValIdx.resize(in.numConstraints);
  for (size_t k = 0; k < in.nnz; ++k) {
    int r = in.aRows[k];
    int col = in.aCols[k];
    if (r < 0 || r >= in.numConstraints || col < 0 || col >= in.numVars) {
      throw std::runtime_error("sparse index out of range");
    }
    data.rowIdx[r].push_back(col);
    data.rowValIdx[r].push_back(k);
  }
  return data;
}

static void add_rational_col(SoPlex &solver, const LPColRational &col) {
  solver.addColRational(col);
}

static void add_rational_col(SPxLPRational &lp, const LPColRational &col) {
  lp.addCol(col);
}

static void add_rational_row(SoPlex &solver, const LPRowRational &row) {
  solver.addRowRational(row);
}

static void add_rational_row(SPxLPRational &lp, const LPRowRational &row) {
  lp.addRow(row);
}

template <typename Lp>
static RationalProblemData build_rational_lp(Lp &lp, const FlatProblemInput &in) {
  RationalProblemData data = parse_rational_problem_data(in);
  DSVectorRational emptyCol(0);
  for (int j = 0; j < in.numVars; ++j) {
    Rational obj(data.cVals[j].q);
    Rational lo = byte_array_u8(in.colLoMask, j)
        ? Rational(Mpq(lean_string_at(in.colLo, j)).q)
        : -Rational(infinity);
    Rational hi = byte_array_u8(in.colHiMask, j)
        ? Rational(Mpq(lean_string_at(in.colHi, j)).q)
        : Rational(infinity);
    add_rational_col(lp, LPColRational(obj, emptyCol, hi, lo));
  }

  for (int i = 0; i < in.numConstraints; ++i) {
    Rational lo = byte_array_u8(in.rowLoMask, i)
        ? Rational(Mpq(lean_string_at(in.rowLo, i)).q)
        : -Rational(infinity);
    Rational hi = byte_array_u8(in.rowHiMask, i)
        ? Rational(Mpq(lean_string_at(in.rowHi, i)).q)
        : Rational(infinity);
    DSVectorRational vals(static_cast<int>(data.rowIdx[i].size()));
    for (size_t t = 0; t < data.rowIdx[i].size(); ++t) {
      vals.add(data.rowIdx[i][t], Rational(data.aVals[data.rowValIdx[i][t]].q));
    }
    add_rational_row(lp, LPRowRational(lo, vals, hi));
  }
  return data;
}

static void build_real_lp(SoPlex &solver, const FlatProblemInput &in) {
  std::vector<double> cVals;
  cVals.reserve(in.numVars);
  for (int j = 0; j < in.numVars; ++j) {
    cVals.push_back(parse_rat_to_double(lean_string_at(in.c, j)));
  }

  std::vector<double> aVals;
  aVals.reserve(in.nnz);
  for (size_t k = 0; k < in.nnz; ++k) {
    aVals.push_back(parse_rat_to_double(lean_string_at(in.aVals, k)));
  }

  DSVector emptyCol(0);
  for (int j = 0; j < in.numVars; ++j) {
    double lo = byte_array_u8(in.colLoMask, j)
        ? parse_rat_to_double(lean_string_at(in.colLo, j))
        : -infinity;
    double hi = byte_array_u8(in.colHiMask, j)
        ? parse_rat_to_double(lean_string_at(in.colHi, j))
        : infinity;
    solver.addColReal(LPCol(cVals[j], emptyCol, hi, lo));
  }

  std::vector<DSVector> rows(in.numConstraints);
  for (size_t k = 0; k < in.nnz; ++k) {
    int r = in.aRows[k];
    int col = in.aCols[k];
    if (r < 0 || r >= in.numConstraints || col < 0 || col >= in.numVars) {
      throw std::runtime_error("sparse index out of range");
    }
    rows[r].add(col, aVals[k]);
  }

  for (int i = 0; i < in.numConstraints; ++i) {
    double lo = byte_array_u8(in.rowLoMask, i)
        ? parse_rat_to_double(lean_string_at(in.rowLo, i))
        : -infinity;
    double hi = byte_array_u8(in.rowHiMask, i)
        ? parse_rat_to_double(lean_string_at(in.rowHi, i))
        : infinity;
    solver.addRowReal(LPRow(lo, rows[i], hi));
  }
}

static lean_object *mk_array_from_mpqs(const std::vector<Mpq> &xs) {
  lean_object *a = lean_alloc_array(xs.size(), xs.size());
  lean_array_set_size(a, xs.size());
  for (size_t i = 0; i < xs.size(); ++i) {
    lean_array_cptr(a)[i] = mk_rat_from_mpq(xs[i].q);
  }
  return a;
}

static lean_object *mk_none() {
  return lean_box(0);
}

static lean_object *mk_some(lean_object *x) {
  lean_object *o = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(o, 0, x);
  return o;
}

static lean_object *mk_dual_bundle(
    const std::vector<Mpq> &rowLower,
    const std::vector<Mpq> &rowUpper,
    const std::vector<Mpq> &colLower,
    const std::vector<Mpq> &colUpper) {
  lean_object *d = lean_alloc_ctor(0, 4, 0);
  lean_ctor_set(d, 0, mk_array_from_mpqs(rowLower));
  lean_ctor_set(d, 1, mk_array_from_mpqs(rowUpper));
  lean_ctor_set(d, 2, mk_array_from_mpqs(colLower));
  lean_ctor_set(d, 3, mk_array_from_mpqs(colUpper));
  return d;
}

static lean_object *mk_certificate(
    lean_object *primalOpt, lean_object *dualOpt, lean_object *rayOpt) {
  lean_object *c = lean_alloc_ctor(0, 3, 0);
  lean_ctor_set(c, 0, primalOpt);
  lean_ctor_set(c, 1, dualOpt);
  lean_ctor_set(c, 2, rayOpt);
  return c;
}

static lean_object *mk_solution(
    uint8_t status, lean_object *objectiveOpt, lean_object *cert,
    const std::string &log) {
  // Solution m n layout (m, n are type-level parameters, erased at
  // runtime). Lean packs scalars at the end:
  //   boxed 0 = objective      : Option Rat
  //   boxed 1 = certificate    : Certificate m n
  //   boxed 2 = log            : String
  //   scalar  = status         : SolveStatus (uint8)
  lean_object *s = lean_alloc_ctor(0, 3, sizeof(uint8_t));
  lean_ctor_set(s, 0, objectiveOpt);
  lean_ctor_set(s, 1, cert);
  lean_ctor_set(s, 2, lean_mk_string(log.c_str()));
  lean_ctor_set_uint8(s, sizeof(void *) * 3, status);
  return s;
}

static lean_object *mk_except_ok(lean_object *x) {
  lean_object *r = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(r, 0, x);
  return r;
}

static lean_object *mk_except_error(const std::string &msg) {
  lean_object *r = lean_alloc_ctor(0, 1, 0);
  lean_ctor_set(r, 0, lean_mk_string(msg.c_str()));
  return r;
}

static void init_mpq_vector(std::vector<Mpq> &xs, size_t n) {
  xs.clear();
  xs.reserve(n);
  for (size_t i = 0; i < n; ++i) xs.emplace_back();
}

static std::vector<Mpq> split_pos(const std::vector<Mpq> &signedVals, bool positivePart) {
  std::vector<Mpq> out;
  init_mpq_vector(out, signedVals.size());
  for (size_t i = 0; i < signedVals.size(); ++i) {
    int cmp = mpq_sgn(signedVals[i].q);
    if ((positivePart && cmp > 0) || (!positivePart && cmp < 0)) {
      mpq_set(out[i].q, signedVals[i].q);
      if (!positivePart) mpq_neg(out[i].q, out[i].q);
    }
  }
  return out;
}

static void negate_all(std::vector<Mpq> &xs) {
  for (auto &x : xs) mpq_neg(x.q, x.q);
}

static void compute_at_y(
    size_t numVars, const int32_t *rows, const int32_t *cols,
    const std::vector<Mpq> &vals, const std::vector<Mpq> &y,
    std::vector<Mpq> &out) {
  init_mpq_vector(out, numVars);
  for (size_t k = 0; k < vals.size(); ++k) {
    mpq_t tmp;
    mpq_init(tmp);
    mpq_mul(tmp, vals[k].q, y[rows[k]].q);
    mpq_add(out[cols[k]].q, out[cols[k]].q, tmp);
    mpq_clear(tmp);
  }
}

static int bound_combination_sign(
    const std::vector<Mpq> &rowSigned, const std::vector<Mpq> &colSigned,
    b_lean_obj_arg rowLoMask, b_lean_obj_arg rowLo,
    b_lean_obj_arg rowHiMask, b_lean_obj_arg rowHi,
    b_lean_obj_arg colLoMask, b_lean_obj_arg colLo,
    b_lean_obj_arg colHiMask, b_lean_obj_arg colHi) {
  Mpq acc;
  mpq_t tmp;
  mpq_init(tmp);
  auto add_bound = [&](const Mpq &signedVal, bool lower, const std::string &bound) {
    if ((lower && mpq_sgn(signedVal.q) <= 0) || (!lower && mpq_sgn(signedVal.q) >= 0)) return;
    Mpq b(bound);
    mpq_mul(tmp, signedVal.q, b.q);
    if (!lower) mpq_neg(tmp, tmp);
    mpq_add(acc.q, acc.q, tmp);
  };
  for (size_t i = 0; i < rowSigned.size(); ++i) {
    if (byte_array_u8(rowLoMask, i)) add_bound(rowSigned[i], true, lean_string_at(rowLo, i));
    if (byte_array_u8(rowHiMask, i)) add_bound(rowSigned[i], false, lean_string_at(rowHi, i));
  }
  for (size_t j = 0; j < colSigned.size(); ++j) {
    if (byte_array_u8(colLoMask, j)) add_bound(colSigned[j], true, lean_string_at(colLo, j));
    if (byte_array_u8(colHiMask, j)) add_bound(colSigned[j], false, lean_string_at(colHi, j));
  }
  int s = mpq_sgn(acc.q);
  mpq_clear(tmp);
  return s;
}

extern "C" LEAN_EXPORT uint32_t lean_soplex_version_ffi(void) {
  return static_cast<uint32_t>(lean_soplex_version());
}

extern "C" LEAN_EXPORT uint32_t lean_soplex_exception_check_ffi(void) {
  return static_cast<uint32_t>(lean_soplex_exception_check());
}

extern "C" LEAN_EXPORT lean_obj_res lean_soplex_solve_exact(
    b_lean_obj_arg /*m*/, b_lean_obj_arg /*n*/,
    uint32_t numVars_u, uint32_t numConstraints_u,
    uint8_t /*sense*/, uint8_t simplex,
    uint8_t hasTimeLimit, double timeLimit,
    uint8_t hasIterLimit, uint32_t iterLimit,
    uint8_t verbose, uint32_t randomSeed,
    uint8_t precisionBoost, uint8_t presolve,
    b_lean_obj_arg c_arr, b_lean_obj_arg objOffset,
    b_lean_obj_arg a_rows_arr, b_lean_obj_arg a_cols_arr, b_lean_obj_arg a_vals_arr,
    b_lean_obj_arg rowLoMask, b_lean_obj_arg rowLo,
    b_lean_obj_arg rowHiMask, b_lean_obj_arg rowHi,
    b_lean_obj_arg colLoMask, b_lean_obj_arg colLo,
    b_lean_obj_arg colHiMask, b_lean_obj_arg colHi) noexcept {
  try {
    const FlatProblemInput input = flat_problem_input(
        numVars_u, numConstraints_u, c_arr, a_rows_arr, a_cols_arr, a_vals_arr,
        rowLoMask, rowLo, rowHiMask, rowHi, colLoMask, colLo, colHiMask, colHi);

    SoPlex solver;
    // Constructed before any parameter / LP-build call so the whole
    // solveExact lifecycle (param-setting warnings, LP construction,
    // optimize, result extraction) writes into the captured buffer
    // when verbose. Non-verbose path is a no-op.
    LogCapture logCap(solver, verbose != 0);
    solver.setIntParam(SoPlex::OBJSENSE, SoPlex::OBJSENSE_MINIMIZE);
    solver.setIntParam(SoPlex::SOLVEMODE, SoPlex::SOLVEMODE_RATIONAL);
    solver.setIntParam(SoPlex::SYNCMODE, SoPlex::SYNCMODE_AUTO);
    // Exact certificates come from the rational refinement/getters. In
    // this Boost/GMP-only build, forcing the floating-point tolerances to
    // literal zero can make the refinement loop stall on tiny examples.
    solver.setIntParam(SoPlex::READMODE, SoPlex::READMODE_RATIONAL);
    solver.setIntParam(SoPlex::CHECKMODE, SoPlex::CHECKMODE_RATIONAL);
    // SoPlex 8.0.2 only enables this knob in MPFR builds. The local
    // static build used by this package is Boost/GMP-only, where setting
    // it to true is rejected by the parameter layer and can leave the
    // solver inconsistent. False is always safe; true keeps SoPlex's
    // build-time default.
    if (!precisionBoost) solver.setBoolParam(SoPlex::PRECISION_BOOSTING, false);
    solver.setIntParam(SoPlex::SIMPLIFIER, presolve ? SoPlex::SIMPLIFIER_INTERNAL : SoPlex::SIMPLIFIER_OFF);
    solver.setIntParam(SoPlex::VERBOSITY, verbose ? SoPlex::VERBOSITY_NORMAL : SoPlex::VERBOSITY_ERROR);
    solver.setRandomSeed(randomSeed);
    if (hasTimeLimit) solver.setRealParam(SoPlex::TIMELIMIT, timeLimit);
    if (hasIterLimit) solver.setIntParam(SoPlex::ITERLIMIT, static_cast<int>(iterLimit));
    if (simplex == 0) solver.setIntParam(SoPlex::ALGORITHM, SoPlex::ALGORITHM_PRIMAL);
    if (simplex == 1) solver.setIntParam(SoPlex::ALGORITHM, SoPlex::ALGORITHM_DUAL);

    RationalProblemData lpData = build_rational_lp(solver, input);

    if (solver.intParam(SoPlex::SYNCMODE) == SoPlex::SYNCMODE_MANUAL) solver.syncLPReal();
    SPxSolver::Status st = solver.optimize();
    uint8_t status = 5; // numericFailure
    lean_object *objective = mk_none();
    lean_object *primal = mk_none();
    lean_object *dual = mk_none();
    lean_object *ray = mk_none();

    auto fetch = [&](size_t n, auto getter, const char *what) {
      std::vector<Mpq> xs;
      init_mpq_vector(xs, n);
      std::unique_ptr<mpq_t[]> raw(new mpq_t[n]);
      for (size_t i = 0; i < n; ++i) mpq_init(raw[i]);
      bool ok = (solver.*getter)(raw.get(), static_cast<int>(n));
      if (!ok) throw std::runtime_error(std::string("SoPlex failed to return ") + what);
      for (size_t i = 0; i < n; ++i) {
        mpq_set(xs[i].q, raw[i]);
        mpq_canonicalize(xs[i].q);
        mpq_clear(raw[i]);
      }
      return xs;
    };

    switch (st) {
      case SPxSolver::OPTIMAL:
      case SPxSolver::OPTIMAL_UNSCALED_VIOLATIONS: {
        status = 0;
        std::ostringstream obj;
        obj << solver.objValueRational();
        objective = mk_some(mk_rat_from_string(obj.str()));
        std::vector<Mpq> x = fetch(input.numVars,
          static_cast<bool (SoPlex::*)(mpq_t *, const int)>(&SoPlex::getPrimalRational),
          "primal solution");
        primal = mk_some(mk_array_from_mpqs(x));
        std::vector<Mpq> y = fetch(input.numConstraints,
          static_cast<bool (SoPlex::*)(mpq_t *, const int)>(&SoPlex::getDualRational),
          "dual solution");
        std::vector<Mpq> z = fetch(input.numVars,
          static_cast<bool (SoPlex::*)(mpq_t *, const int)>(&SoPlex::getRedCostRational),
          "reduced costs");
        auto rowLower = split_pos(y, true);
        auto rowUpper = split_pos(y, false);
        auto colLower = split_pos(z, true);
        auto colUpper = split_pos(z, false);
        dual = mk_some(mk_dual_bundle(rowLower, rowUpper, colLower, colUpper));
        break;
      }
      case SPxSolver::INFEASIBLE: {
        status = 1;
        std::vector<Mpq> y = fetch(input.numConstraints,
          static_cast<bool (SoPlex::*)(mpq_t *, const int)>(&SoPlex::getDualFarkasRational),
          "dual Farkas vector");
        std::vector<Mpq> aty;
        compute_at_y(input.numVars, input.aRows, input.aCols, lpData.aVals, y, aty);
        for (auto &v : aty) mpq_neg(v.q, v.q);
        if (bound_combination_sign(y, aty, rowLoMask, rowLo, rowHiMask, rowHi,
                                   colLoMask, colLo, colHiMask, colHi) < 0) {
          negate_all(y);
          negate_all(aty);
        }
        auto rowLower = split_pos(y, true);
        auto rowUpper = split_pos(y, false);
        auto colLower = split_pos(aty, true);
        auto colUpper = split_pos(aty, false);
        dual = mk_some(mk_dual_bundle(rowLower, rowUpper, colLower, colUpper));
        break;
      }
      case SPxSolver::UNBOUNDED: {
        status = 2;
        std::vector<Mpq> x = fetch(input.numVars,
          static_cast<bool (SoPlex::*)(mpq_t *, const int)>(&SoPlex::getPrimalRational),
          "primal base point");
        std::vector<Mpq> r = fetch(input.numVars,
          static_cast<bool (SoPlex::*)(mpq_t *, const int)>(&SoPlex::getPrimalRayRational),
          "primal ray");
        primal = mk_some(mk_array_from_mpqs(x));
        ray = mk_some(mk_array_from_mpqs(r));
        break;
      }
      case SPxSolver::ABORT_TIME:
        status = 3;
        break;
      case SPxSolver::ABORT_ITER:
        status = 4;
        break;
      case SPxSolver::ABORT_VALUE:
      case SPxSolver::SINGULAR:
      case SPxSolver::NO_RATIOTESTER:
      case SPxSolver::REGULAR:
        status = 5;
        break;
      default:
        status = 7;
        break;
    }

    lean_object *cert = mk_certificate(primal, dual, ray);
    lean_object *sol = mk_solution(status, objective, cert, logCap.str());
    return mk_except_ok(sol);
  } catch (const std::exception &e) {
    return mk_except_error(e.what());
  } catch (...) {
    return mk_except_error("unknown C++ exception");
  }
}

/*
 * Build a `some : Float → Option Float` Lean value. `Option` is a
 * universe-polymorphic inductive, so its data argument is always
 * passed as a boxed `lean_object *` — the `some` constructor has one
 * object field, never a scalar Float slot. We therefore box the
 * double with `lean_box_float` before storing.
 */
static lean_object *mk_some_float(double d) {
  lean_object *o = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(o, 0, lean_box_float(d));
  return o;
}

/*
 * Build a Lean `FloatSolution` value. The declaration is
 *   structure FloatSolution where
 *     status      : SolveStatus       -- enum, 1 scalar byte
 *     primalAsRat : Option (Array Rat)
 *     objective   : Option Float
 *     log         : String
 * Lean places object fields first (in declaration order), then scalars.
 * So the ctor has 3 object slots followed by 1 byte of scalar data.
 */
static lean_object *mk_float_solution(
    uint8_t status, lean_object *primalOpt, lean_object *objectiveOpt,
    const std::string &log) {
  lean_object *s = lean_alloc_ctor(0, 3, sizeof(uint8_t));
  lean_ctor_set(s, 0, primalOpt);
  lean_ctor_set(s, 1, objectiveOpt);
  lean_ctor_set(s, 2, lean_mk_string(log.c_str()));
  lean_ctor_set_uint8(s, sizeof(void *) * 3, status);
  return s;
}

/*
 * Float-mode solve. Mirrors `lean_soplex_solve_exact` structurally but
 * builds the LP via `addColReal` / `addRowReal` and runs SoPlex in its
 * default floating-point mode. The returned `primalAsRat` is the exact
 * rational representation of each IEEE-754 double SoPlex produced
 * (via `mpq_set_d`), not a decimal rational and not a verifier-grade
 * certificate.
 *
 * Marshalling helpers (`Mpq`, `mk_rat_from_mpq`, `mk_array_from_mpqs`,
 * `mk_some` / `mk_none`, `mk_except_*`, `lean_string_at`,
 * `byte_array_*`) are shared with `lean_soplex_solve_exact` above.
 */
extern "C" LEAN_EXPORT lean_obj_res lean_soplex_solve_float(
    b_lean_obj_arg /*n*/,
    uint32_t numVars_u, uint32_t numConstraints_u,
    uint8_t /*sense*/, uint8_t simplex,
    uint8_t hasTimeLimit, double timeLimit,
    uint8_t hasIterLimit, uint32_t iterLimit,
    uint8_t verbose, uint32_t randomSeed,
    uint8_t presolve,
    b_lean_obj_arg c_arr, b_lean_obj_arg /*objOffset*/,
    b_lean_obj_arg a_rows_arr, b_lean_obj_arg a_cols_arr, b_lean_obj_arg a_vals_arr,
    b_lean_obj_arg rowLoMask, b_lean_obj_arg rowLo,
    b_lean_obj_arg rowHiMask, b_lean_obj_arg rowHi,
    b_lean_obj_arg colLoMask, b_lean_obj_arg colLo,
    b_lean_obj_arg colHiMask, b_lean_obj_arg colHi) noexcept {
  try {
    const FlatProblemInput input = flat_problem_input(
        numVars_u, numConstraints_u, c_arr, a_rows_arr, a_cols_arr, a_vals_arr,
        rowLoMask, rowLo, rowHiMask, rowHi, colLoMask, colLo, colHiMask, colHi);

    SoPlex solver;
    LogCapture logCap(solver, verbose != 0);
    solver.setIntParam(SoPlex::OBJSENSE, SoPlex::OBJSENSE_MINIMIZE);
    solver.setIntParam(SoPlex::SIMPLIFIER,
        presolve ? SoPlex::SIMPLIFIER_INTERNAL : SoPlex::SIMPLIFIER_OFF);
    solver.setIntParam(SoPlex::VERBOSITY,
        verbose ? SoPlex::VERBOSITY_NORMAL : SoPlex::VERBOSITY_ERROR);
    solver.setRandomSeed(randomSeed);
    if (hasTimeLimit) solver.setRealParam(SoPlex::TIMELIMIT, timeLimit);
    if (hasIterLimit) solver.setIntParam(SoPlex::ITERLIMIT, static_cast<int>(iterLimit));
    if (simplex == 0) solver.setIntParam(SoPlex::ALGORITHM, SoPlex::ALGORITHM_PRIMAL);
    if (simplex == 1) solver.setIntParam(SoPlex::ALGORITHM, SoPlex::ALGORITHM_DUAL);

    build_real_lp(solver, input);

    SPxSolver::Status st = solver.optimize();
    uint8_t status = 5; // numericFailure
    lean_object *primal = mk_none();
    lean_object *objective = mk_none();

    switch (st) {
      case SPxSolver::OPTIMAL:
      case SPxSolver::OPTIMAL_UNSCALED_VIOLATIONS: {
        status = 0;
        std::vector<double> x(input.numVars);
        if (!solver.getPrimalReal(x.data(), input.numVars)) {
          throw std::runtime_error("SoPlex failed to return primal solution");
        }
        lean_object *arr = lean_alloc_array(input.numVars, input.numVars);
        lean_array_set_size(arr, input.numVars);
        for (int j = 0; j < input.numVars; ++j) {
          lean_array_cptr(arr)[j] = mk_rat_from_double(x[j]);
        }
        primal = mk_some(arr);
        objective = mk_some_float(solver.objValueReal());
        break;
      }
      case SPxSolver::INFEASIBLE:
        status = 1;
        break;
      case SPxSolver::UNBOUNDED:
        status = 2;
        break;
      case SPxSolver::ABORT_TIME:
        status = 3;
        break;
      case SPxSolver::ABORT_ITER:
        status = 4;
        break;
      case SPxSolver::ABORT_VALUE:
      case SPxSolver::SINGULAR:
      case SPxSolver::NO_RATIOTESTER:
      case SPxSolver::REGULAR:
        status = 5;
        break;
      default:
        status = 7;
        break;
    }

    return mk_except_ok(mk_float_solution(status, primal, objective, logCap.str()));
  } catch (const std::exception &e) {
    return mk_except_error(e.what());
  } catch (...) {
    return mk_except_error("unknown C++ exception");
  }
}

/*
 * FFI-check toy LP solve. Inputs:
 *   c          : FloatArray of length numVars
 *   b          : FloatArray of length numConstraints
 *   a_rows     : ByteArray of int32 of length a_nnz
 *   a_cols     : ByteArray of int32 of length a_nnz
 *   a_vals     : FloatArray of length a_nnz
 *
 * Returns a Lean structure
 *   { primal : FloatArray
 *     ret    : UInt32           -- 0 ok, 1 infeas, 2 unbounded, ~0 error
 *     obj    : Float }
 *
 * `ret = (uint32_t)-1` (i.e. 0xFFFFFFFF) is reserved for any FFI-layer or
 * SoPlex error that didn't terminate normally.
 */
extern "C" LEAN_EXPORT lean_obj_res lean_soplex_ffi_check_solve_ffi(
    b_lean_obj_arg c_arr,
    b_lean_obj_arg b_arr,
    b_lean_obj_arg a_rows,
    b_lean_obj_arg a_cols,
    b_lean_obj_arg a_vals) {
  const int32_t numVars = static_cast<int32_t>(lean_sarray_size(c_arr));
  const int32_t numConstraints = static_cast<int32_t>(lean_sarray_size(b_arr));
  const int32_t a_nnz = static_cast<int32_t>(lean_sarray_size(a_rows) / sizeof(int32_t));

  lean_object *primal_out =
      lean_alloc_sarray(sizeof(double), static_cast<size_t>(numVars),
                        static_cast<size_t>(numVars));
  double *primal_ptr = reinterpret_cast<double *>(lean_sarray_cptr(primal_out));
  double objval = 0.0;

  int rc = lean_soplex_ffi_check_solve(
      numVars, numConstraints,
      float_array_const_ptr(c_arr),
      float_array_const_ptr(b_arr),
      a_nnz,
      byte_array_as_i32(a_rows),
      byte_array_as_i32(a_cols),
      float_array_const_ptr(a_vals),
      primal_ptr,
      &objval);

  /*
   * Layout for `Soplex.FfiCheckResult`:
   *   primal : FloatArray   -- object field
   *   ret    : UInt32       -- scalar field
   *   obj    : Float        -- scalar field
   *
   * Lean places object fields first (declaration order), then scalar
   * fields ordered by descending alignment requirement. With one
   * object slot (`primal`) and two scalars, the scalar region starts
   * at byte offset `sizeof(void*) * 1`. Within the scalar region,
   * `Float` (align 8) precedes `UInt32` (align 4).
   */
  lean_object *result =
      lean_alloc_ctor(0, /*num_objs=*/1, /*scalar_bytes=*/sizeof(double) + sizeof(uint32_t));
  lean_ctor_set(result, 0, primal_out);
  lean_ctor_set_float(result, sizeof(void *), objval);
  lean_ctor_set_uint32(result, sizeof(void *) + sizeof(double), static_cast<uint32_t>(rc));
  return result;
}

// ---------------------------------------------------------------------------
// MPS / LP file I/O.
//
// We use SoPlex's `SPxLPBase<Rational>` (a.k.a. `SPxLPRational`) directly
// rather than going through the top-level `SoPlex::readFile` / `writeFile`
// surface. Two reasons:
//
//  * Explicit format control. `SoPlex::readFile` dispatches on the
//    `READMODE` parameter (REAL vs RATIONAL precision), and
//    `writeFile`/`writeFileLPBase` dispatches LP vs MPS purely by the
//    `.lp` / `.mps` filename suffix. We want the caller's choice of
//    `readMps` / `readLp` / `writeMps` / `writeLp` to be honoured
//    regardless of file extension.
//  * `SPxLPBase<Rational>::readLPF` / `readMPS` / `writeLPF` / `writeMPS`
//    are the natural format-specific entry points and they operate
//    directly on the rational LP we want.
//
// Round-trip note: ranged rows survive MPS round-trip (RANGES section)
// but `writeLPF` expands a ranged row into two non-ranged rows. That's a
// SoPlex format-conversion property, not a bridge property; we don't
// paper over it.
// ---------------------------------------------------------------------------

using SPxLPRat = SPxLPBase<Rational>;

static lean_object *mk_nat_from_int(int n) {
  return lean_unsigned_to_nat(static_cast<unsigned>(n));
}

static lean_object *mk_prod2(lean_object *a, lean_object *b) {
  lean_object *p = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p, 0, a);
  lean_ctor_set(p, 1, b);
  return p;
}

static std::string rational_to_string(const Rational &r) {
  std::ostringstream os;
  os << r;
  return os.str();
}

static bool is_neg_infinity(const Rational &r) {
  return r <= Rational(-infinity);
}

static bool is_pos_infinity(const Rational &r) {
  return r >= Rational(infinity);
}

// Optional<String> representing a finite lower bound: empty string ⇔ none.
// Decoupled from Lean allocation so we can do all C++-side / GMP-side
// work (which is the throw-prone half) before any Lean ctor allocation.
static std::string opt_lower_str(const Rational &r) {
  return is_neg_infinity(r) ? std::string() : rational_to_string(r);
}

static std::string opt_upper_str(const Rational &r) {
  return is_pos_infinity(r) ? std::string() : rational_to_string(r);
}

// Build an `Option Rat` Lean object from the encoded-string form above.
static lean_object *mk_opt_rat(const std::string &s, bool present) {
  return present ? mk_some(mk_rat_from_string(s)) : mk_none();
}

// Construct a `Soplex.Problem` Lean object.
//
// `Problem m n` is a structure with the following fields in
// declaration order; Lean lays out a structure as a single anonymous
// constructor with one argument slot per field. `m` and `n` are
// type-level naturals, erased at runtime:
//
//   c              : Vector Rat n         (runtime: Array Rat)
//   objOffset      : Rat
//   a              : Array (Nat × Nat × Rat)
//   rowBounds      : Vector (Option Rat × Option Rat) m   (Array layout)
//   colBounds      : Vector (Option Rat × Option Rat) n   (Array layout)
static lean_object *mk_problem(
    lean_object *c, lean_object *objOffset,
    lean_object *a, lean_object *rowBounds, lean_object *colBounds) {
  lean_object *p = lean_alloc_ctor(0, 5, 0);
  lean_ctor_set(p, 0, c);
  lean_ctor_set(p, 1, objOffset);
  lean_ctor_set(p, 2, a);
  lean_ctor_set(p, 3, rowBounds);
  lean_ctor_set(p, 4, colBounds);
  return p;
}

// Walk an `SPxLPBase<Rational>` (already filled by `readLPF` / `readMPS`)
// into our canonical `Problem` shape.
//
// SoPlex stores LPs internally in maximisation form, but `obj(j)`
// returns the coefficient *as the file wrote it* regardless of sense
// (it negates twice — once because storage is in max form, once because
// the user-facing sense maps it back). Our `Problem` is always
// interpreted as a minimisation problem (sense lives in `Options`), so
// if the file said `Maximize` we must negate every objective coefficient
// and the offset by hand. We do NOT call `lp.changeSense(MINIMIZE)` —
// it would also flip the internal storage and re-apply on the next
// `obj()` call, undoing exactly the change we want.
//
// Exception-safety note: every Rational is converted to its decimal
// string representation in a first pass (this is where GMP / `mpq_get_str`
// can throw). Only once all strings are in hand do we allocate Lean
// constructors; from that point on we never throw, so partially built
// Lean objects cannot leak.
static lean_object *problem_from_lp(SPxLPRat &lp) {
  const bool isMax = (lp.spxSense() == SPxLPRat::MAXIMIZE);
  const int nVars = lp.nCols();
  const int nCons = lp.nRows();

  // Phase 1 — pull every Rational out as a std::string. Throws stay in
  // this phase, before any Lean allocation has happened.
  auto signedRat = [&](const Rational &r) -> std::string {
    return isMax ? rational_to_string(-r) : rational_to_string(r);
  };

  std::string offsetStr = signedRat(lp.objOffset());
  std::vector<std::string> cStrs(nVars);
  for (int j = 0; j < nVars; ++j) cStrs[j] = signedRat(lp.obj(j));

  std::vector<std::pair<std::string, std::string>> colBoundStrs(nVars);
  std::vector<std::pair<bool, bool>> colBoundPresent(nVars);
  for (int j = 0; j < nVars; ++j) {
    const Rational &lo = lp.lower(j);
    const Rational &hi = lp.upper(j);
    colBoundPresent[j] = {!is_neg_infinity(lo), !is_pos_infinity(hi)};
    colBoundStrs[j] = {opt_lower_str(lo), opt_upper_str(hi)};
  }

  std::vector<std::pair<std::string, std::string>> rowBoundStrs(nCons);
  std::vector<std::pair<bool, bool>> rowBoundPresent(nCons);
  // (row, col, value-string) — note the value strings, not Rationals.
  std::vector<std::tuple<int, int, std::string>> entries;
  for (int i = 0; i < nCons; ++i) {
    const Rational &lhs = lp.lhs(i);
    const Rational &rhs = lp.rhs(i);
    rowBoundPresent[i] = {!is_neg_infinity(lhs), !is_pos_infinity(rhs)};
    rowBoundStrs[i] = {opt_lower_str(lhs), opt_upper_str(rhs)};
    const SVectorRational &row = lp.rowVector(i);
    for (int k = 0; k < row.size(); ++k) {
      entries.emplace_back(i, row.index(k), rational_to_string(row.value(k)));
    }
  }

  // Phase 2 — pure Lean allocations. lean_alloc_* terminate on OOM
  // rather than throwing, and `mk_rat_from_string` on a well-formed
  // decimal string is non-throwing, so partial-allocation leaks are
  // ruled out.
  lean_object *cArr = lean_alloc_array(static_cast<size_t>(nVars), static_cast<size_t>(nVars));
  lean_array_set_size(cArr, static_cast<size_t>(nVars));
  for (int j = 0; j < nVars; ++j) {
    lean_array_cptr(cArr)[j] = mk_rat_from_string(cStrs[j]);
  }

  lean_object *colB = lean_alloc_array(static_cast<size_t>(nVars), static_cast<size_t>(nVars));
  lean_array_set_size(colB, static_cast<size_t>(nVars));
  for (int j = 0; j < nVars; ++j) {
    lean_object *lo = mk_opt_rat(colBoundStrs[j].first, colBoundPresent[j].first);
    lean_object *hi = mk_opt_rat(colBoundStrs[j].second, colBoundPresent[j].second);
    lean_array_cptr(colB)[j] = mk_prod2(lo, hi);
  }

  lean_object *rowB = lean_alloc_array(static_cast<size_t>(nCons), static_cast<size_t>(nCons));
  lean_array_set_size(rowB, static_cast<size_t>(nCons));
  for (int i = 0; i < nCons; ++i) {
    lean_object *lo = mk_opt_rat(rowBoundStrs[i].first, rowBoundPresent[i].first);
    lean_object *hi = mk_opt_rat(rowBoundStrs[i].second, rowBoundPresent[i].second);
    lean_array_cptr(rowB)[i] = mk_prod2(lo, hi);
  }

  const size_t nnz = entries.size();
  lean_object *aArr = lean_alloc_array(nnz, nnz);
  lean_array_set_size(aArr, nnz);
  for (size_t k = 0; k < nnz; ++k) {
    const auto &e = entries[k];
    lean_object *triple = mk_prod2(
        mk_nat_from_int(std::get<0>(e)),
        mk_prod2(mk_nat_from_int(std::get<1>(e)),
                 mk_rat_from_string(std::get<2>(e))));
    lean_array_cptr(aArr)[k] = triple;
  }

  lean_object *prob = mk_problem(
      cArr, mk_rat_from_string(offsetStr),
      aArr, rowB, colB);
  // Wrap in `Σ m, Σ n, Problem m n` so `readMpsImpl` / `readLpImpl`
  // can return the dimensions as type-level witnesses.
  //   inner = Sigma.mk nVars prob   (n is the outer Nat in the type
  //                                  `Σ n, Problem m n`)
  //   outer = Sigma.mk nCons inner
  lean_object *inner = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(inner, 0, mk_nat_from_int(nVars));
  lean_ctor_set(inner, 1, prob);
  lean_object *outer = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(outer, 0, mk_nat_from_int(nCons));
  lean_ctor_set(outer, 1, inner);
  return outer;
}

enum class LpFormat { LP, MPS };

static lean_obj_res read_lp_file(b_lean_obj_arg path_obj, LpFormat fmt) noexcept {
  try {
    const char *path = lean_string_cstr(path_obj);
    std::ifstream in(path);
    if (!in) {
      return mk_except_error(std::string("cannot open file for read: ") + path);
    }
    SPxLPRat lp;
    // SoPlex's reader/writer emit warnings via `SPX_MSG_WARNING((*spxout),
    // ...)` which dereferences `spxout`. The default `SPxLPBase` ctor
    // leaves `spxout` as `nullptr` (the `SoPlex` class normally wires
    // its own SPxOut into the LP it owns), so standalone construction
    // segfaults on the first warning. Give it a local sink; verbosity
    // is set to ERROR so nothing actually prints unless the format
    // parser is shouting about a real problem.
    SPxOut spxout;
    spxout.setVerbosity(SPxOut::VERB_ERROR);
    lp.setOutstream(spxout);
    NameSet rowNames;
    NameSet colNames;
    DIdxSet intVars;
    const bool ok = (fmt == LpFormat::MPS)
        ? lp.readMPS(in, &rowNames, &colNames, &intVars)
        : lp.readLPF(in, &rowNames, &colNames, &intVars);
    if (!ok) {
      return mk_except_error(std::string("SoPlex failed to parse ")
                             + (fmt == LpFormat::MPS ? "MPS" : "LP")
                             + " file: " + path);
    }
    // Integer-marked variables would relax silently to continuous,
    // changing the problem's meaning. Reject them; `Problem` has no
    // integrality field, so we cannot faithfully represent them.
    if (intVars.size() > 0) {
      return mk_except_error(
          std::string("integer variables are not supported (file: ") + path + ")");
    }
    return mk_except_ok(problem_from_lp(lp));
  } catch (const std::exception &e) {
    return mk_except_error(e.what());
  } catch (...) {
    return mk_except_error("unknown C++ exception");
  }
}

// Build an `SPxLPBase<Rational>` from the flat Problem marshalling and
// stream it out via `writeMPS` / `writeLPF`. Mirrors `lean_soplex_solve_exact`'s
// LP-construction path (same `addColRational` / `addRowRational` shape,
// same handling of optional bound masks) but does not call `optimize`.
static lean_obj_res write_lp_file(
    b_lean_obj_arg path_obj,
    uint32_t numVars_u, uint32_t numConstraints_u,
    b_lean_obj_arg c_arr, b_lean_obj_arg objOffset_str,
    b_lean_obj_arg a_rows_arr, b_lean_obj_arg a_cols_arr, b_lean_obj_arg a_vals_arr,
    b_lean_obj_arg rowLoMask, b_lean_obj_arg rowLo,
    b_lean_obj_arg rowHiMask, b_lean_obj_arg rowHi,
    b_lean_obj_arg colLoMask, b_lean_obj_arg colLo,
    b_lean_obj_arg colHiMask, b_lean_obj_arg colHi,
    LpFormat fmt) noexcept {
  try {
    const char *path = lean_string_cstr(path_obj);
    const FlatProblemInput input = flat_problem_input(
        numVars_u, numConstraints_u, c_arr, a_rows_arr, a_cols_arr, a_vals_arr,
        rowLoMask, rowLo, rowHiMask, rowHi, colLoMask, colLo, colHiMask, colHi);

    SPxLPRat lp;
    // See `read_lp_file` for why this `SPxOut` is necessary.
    SPxOut spxout;
    spxout.setVerbosity(SPxOut::VERB_ERROR);
    lp.setOutstream(spxout);
    lp.changeSense(SPxLPRat::MINIMIZE);

    build_rational_lp(lp, input);

    // SoPlex's `writeLPF` and `writeMPS` for `Rational` do not emit
    // `objOffset` (LP format has no syntax for it; MPS *can* express it
    // via an RHS row against the N-row, which SoPlex reads but does not
    // write). Silently dropping a nonzero offset on write would produce
    // a file whose round-trip is mathematically wrong, so reject up
    // front. Callers can rewrite the offset into an explicit auxiliary
    // variable if they really need it on disk.
    Mpq off(std::string(lean_string_cstr(objOffset_str)));
    if (mpq_sgn(off.q) != 0) {
      return mk_except_error(
          "nonzero objOffset is not supported by SoPlex's MPS / LP writers; "
          "rewrite as an auxiliary variable before writing");
    }

    std::ofstream out(path);
    if (!out) {
      return mk_except_error(std::string("cannot open file for write: ") + path);
    }
    if (fmt == LpFormat::MPS) {
      lp.writeMPS(out, nullptr, nullptr, nullptr, /*writeZeroObjective=*/true);
    } else {
      lp.writeLPF(out, nullptr, nullptr, nullptr, /*writeZeroObjective=*/true);
    }
    if (!out) {
      return mk_except_error(std::string("error writing file: ") + path);
    }
    return mk_except_ok(lean_box(0));
  } catch (const std::exception &e) {
    return mk_except_error(e.what());
  } catch (...) {
    return mk_except_error("unknown C++ exception");
  }
}

extern "C" LEAN_EXPORT lean_obj_res lean_soplex_read_mps_ffi(b_lean_obj_arg path_obj) noexcept {
  return read_lp_file(path_obj, LpFormat::MPS);
}

extern "C" LEAN_EXPORT lean_obj_res lean_soplex_read_lp_ffi(b_lean_obj_arg path_obj) noexcept {
  return read_lp_file(path_obj, LpFormat::LP);
}

extern "C" LEAN_EXPORT lean_obj_res lean_soplex_write_mps_ffi(
    b_lean_obj_arg path_obj,
    uint32_t numVars_u, uint32_t numConstraints_u,
    b_lean_obj_arg c_arr, b_lean_obj_arg objOffset_str,
    b_lean_obj_arg a_rows_arr, b_lean_obj_arg a_cols_arr, b_lean_obj_arg a_vals_arr,
    b_lean_obj_arg rowLoMask, b_lean_obj_arg rowLo,
    b_lean_obj_arg rowHiMask, b_lean_obj_arg rowHi,
    b_lean_obj_arg colLoMask, b_lean_obj_arg colLo,
    b_lean_obj_arg colHiMask, b_lean_obj_arg colHi) noexcept {
  return write_lp_file(path_obj, numVars_u, numConstraints_u, c_arr, objOffset_str,
                       a_rows_arr, a_cols_arr, a_vals_arr,
                       rowLoMask, rowLo, rowHiMask, rowHi,
                       colLoMask, colLo, colHiMask, colHi, LpFormat::MPS);
}

extern "C" LEAN_EXPORT lean_obj_res lean_soplex_write_lp_ffi(
    b_lean_obj_arg path_obj,
    uint32_t numVars_u, uint32_t numConstraints_u,
    b_lean_obj_arg c_arr, b_lean_obj_arg objOffset_str,
    b_lean_obj_arg a_rows_arr, b_lean_obj_arg a_cols_arr, b_lean_obj_arg a_vals_arr,
    b_lean_obj_arg rowLoMask, b_lean_obj_arg rowLo,
    b_lean_obj_arg rowHiMask, b_lean_obj_arg rowHi,
    b_lean_obj_arg colLoMask, b_lean_obj_arg colLo,
    b_lean_obj_arg colHiMask, b_lean_obj_arg colHi) noexcept {
  return write_lp_file(path_obj, numVars_u, numConstraints_u, c_arr, objOffset_str,
                       a_rows_arr, a_cols_arr, a_vals_arr,
                       rowLoMask, rowLo, rowHiMask, rowHi,
                       colLoMask, colLo, colHiMask, colHi, LpFormat::LP);
}
