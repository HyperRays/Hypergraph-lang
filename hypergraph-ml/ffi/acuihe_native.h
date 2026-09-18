#ifndef ACUIHE_NATIVE_H
#define ACUIHE_NATIVE_H

#include <lean/lean.h>
#include <stdint.h>

/* Versioned Lean ABI. All lean_object arguments are consumed; return values
   own one reference. USize parameters are unboxed size_t values. The API and
   Lean runtime must be built using lean/lean-toolchain together. */
lean_obj_res initialize_HypergraphFFI_HypergraphFFI(uint8_t builtin);
uint32_t acuihe_v1_abi_version(lean_obj_arg unit);
lean_obj_res acuihe_v1_zero(lean_obj_arg unit);
lean_obj_res acuihe_v1_constant(size_t name);
lean_obj_res acuihe_v1_variable(size_t name);
lean_obj_res acuihe_v1_add(lean_obj_arg left, lean_obj_arg right);
lean_obj_res acuihe_v1_hom(size_t name, lean_obj_arg body);
lean_obj_res acuihe_v1_free(lean_obj_arg body);
uint8_t acuihe_v1_equal(lean_obj_arg left, lean_obj_arg right);
uint8_t acuihe_v1_below(lean_obj_arg left, lean_obj_arg right);
lean_obj_res acuihe_v1_normalize(lean_obj_arg term);
uint8_t acuihe_v1_graph_equal(lean_obj_arg left, lean_obj_arg right);
uint8_t acuihe_v1_graph_below(lean_obj_arg left, lean_obj_arg right);
lean_obj_res acuihe_v1_graph_layer(lean_obj_arg graph);
uint8_t acuihe_v1_is_unifiable(lean_obj_arg equations);
lean_obj_res acuihe_v1_solve(lean_obj_arg equations);
lean_obj_res acuihe_v1_solution_get(lean_obj_arg solution, size_t name);

#endif
