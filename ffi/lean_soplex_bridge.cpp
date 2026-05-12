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

#include <lean/lean.h>

#include "lean_soplex.h"

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

extern "C" LEAN_EXPORT uint32_t lean_soplex_version_ffi(void) {
  return static_cast<uint32_t>(lean_soplex_version());
}

extern "C" LEAN_EXPORT uint32_t lean_soplex_exception_check_ffi(void) {
  return static_cast<uint32_t>(lean_soplex_exception_check());
}

/*
 * Smoke solve. Inputs:
 *   c          : FloatArray of length numVars
 *   b          : FloatArray of length numConstraints
 *   a_rows     : ByteArray of int32 of length a_nnz
 *   a_cols     : ByteArray of int32 of length a_nnz
 *   a_vals     : FloatArray of length a_nnz
 *
 * Returns a Lean structure
 *   { ret    : UInt32           -- 0 ok, 1 infeas, 2 unbounded, ~0 error
 *     obj    : Float
 *     primal : FloatArray }
 *
 * `ret = (uint32_t)-1` (i.e. 0xFFFFFFFF) is reserved for any bridge or
 * SoPlex error that didn't terminate normally.
 */
extern "C" LEAN_EXPORT lean_obj_res lean_soplex_smoke_solve_ffi(
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

  int rc = lean_soplex_smoke_solve(
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
   * Layout for `LeanSoplex.SmokeResult`:
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
