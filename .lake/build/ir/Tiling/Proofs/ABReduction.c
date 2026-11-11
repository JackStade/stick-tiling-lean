// Lean compiler output
// Module: Tiling.Proofs.ABReduction
// Imports: public import Init public meta import Init public import Tiling.Proofs.ReductionCompute
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
uint8_t l_List_instDecidableEqNil___redArg(lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_abSpecData(lean_object*);
extern lean_object* lp_Tiling_StickPolyhex_ABSim_emptySpecData;
lean_object* lp_Tiling_StickPolyhex_GapSpecData_markData(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_reduceABSpecData(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_reduceABStick(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_reduceABSpecData(lean_object* v_S_1_){
_start:
{
lean_object* v_A_2_; lean_object* v_B_3_; uint8_t v___x_4_; 
v_A_2_ = lean_ctor_get(v_S_1_, 0);
v_B_3_ = lean_ctor_get(v_S_1_, 1);
v___x_4_ = l_List_instDecidableEqNil___redArg(v_A_2_);
if (v___x_4_ == 0)
{
uint8_t v___x_5_; 
v___x_5_ = l_List_instDecidableEqNil___redArg(v_B_3_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; 
v___x_6_ = lp_Tiling_StickPolyhex_ABSim_abSpecData(v_S_1_);
return v___x_6_;
}
else
{
lean_object* v___x_7_; 
lean_dec_ref(v_S_1_);
v___x_7_ = lp_Tiling_StickPolyhex_ABSim_emptySpecData;
return v___x_7_;
}
}
else
{
lean_object* v___x_8_; 
lean_dec_ref(v_S_1_);
v___x_8_ = lp_Tiling_StickPolyhex_ABSim_emptySpecData;
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_reduceABStick(lean_object* v_S_9_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lp_Tiling_StickPolyhex_ABSim_reduceABSpecData(v_S_9_);
v___x_11_ = lp_Tiling_StickPolyhex_GapSpecData_markData(v___x_10_);
lean_dec_ref(v___x_10_);
return v___x_11_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_ReductionCompute(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_Proofs_ABReduction(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_ReductionCompute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
