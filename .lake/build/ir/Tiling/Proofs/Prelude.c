// Lean compiler output
// Module: Tiling.Proofs.Prelude
// Imports: public import Init public meta import Init public import Mathlib.Data.Finset.Card public import Mathlib.Data.Int.Interval public import Mathlib.Data.Int.ModEq public import Mathlib.Computability.Primrec.List public import Mathlib.Computability.Reduce public import Mathlib.Logic.Relation public import Mathlib.Tactic.Abel public import Mathlib.Tactic.Choose public import Mathlib.Tactic.Convert public import Mathlib.Tactic.IntervalCases public import Mathlib.Tactic.Linarith public import Mathlib.Tactic.LinearCombination public import Mathlib.Tactic.NormNum public import Mathlib.Tactic.Positivity public import Mathlib.Tactic.Push public import Mathlib.Tactic.Ring public import Mathlib.Tactic.SplitIfs public import Mathlib.Tactic.Tauto
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Card(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Int_Interval(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Int_ModEq(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Computability_Primrec_List(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Computability_Reduce(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Logic_Relation(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic_Abel(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic_Choose(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic_Convert(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic_IntervalCases(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic_Linarith(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic_LinearCombination(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic_NormNum(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic_Positivity(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic_Push(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic_Ring(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic_SplitIfs(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic_Tauto(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_Proofs_Prelude(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Finset_Card(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Int_Interval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Int_ModEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Computability_Primrec_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Computability_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Logic_Relation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic_Abel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic_Choose(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic_Convert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic_IntervalCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic_Linarith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic_LinearCombination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic_NormNum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic_Positivity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic_Push(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic_SplitIfs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic_Tauto(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
