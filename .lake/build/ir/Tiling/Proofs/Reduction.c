// Lean compiler output
// Module: Tiling.Proofs.Reduction
// Imports: public import Init public meta import Init public import Tiling.Proofs.ABSpecEquiv public import Tiling.Proofs.ABMain
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
lean_object* lp_Tiling_Tiling_AB_reduceAB(lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_abSpecData(lean_object*);
lean_object* lp_Tiling_StickPolyhex_GapSpecData_markData(lean_object*);
static const lean_ctor_object lp_Tiling_StickPolyhex_ABSim_emptySpecData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_Tiling_StickPolyhex_ABSim_emptySpecData___closed__0 = (const lean_object*)&lp_Tiling_StickPolyhex_ABSim_emptySpecData___closed__0_value;
LEAN_EXPORT const lean_object* lp_Tiling_StickPolyhex_ABSim_emptySpecData = (const lean_object*)&lp_Tiling_StickPolyhex_ABSim_emptySpecData___closed__0_value;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_reduceSpecData(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_reduceStick(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_reduceSpecData(lean_object* v_T_5_){
_start:
{
uint8_t v___x_6_; 
v___x_6_ = l_List_instDecidableEqNil___redArg(v_T_5_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lp_Tiling_Tiling_AB_reduceAB(v_T_5_);
v___x_8_ = lp_Tiling_StickPolyhex_ABSim_abSpecData(v___x_7_);
return v___x_8_;
}
else
{
lean_object* v___x_9_; 
lean_dec(v_T_5_);
v___x_9_ = ((lean_object*)(lp_Tiling_StickPolyhex_ABSim_emptySpecData));
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_reduceStick(lean_object* v_T_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lp_Tiling_StickPolyhex_ABSim_reduceSpecData(v_T_10_);
v___x_12_ = lp_Tiling_StickPolyhex_GapSpecData_markData(v___x_11_);
lean_dec_ref(v___x_11_);
return v___x_12_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_ABSpecEquiv(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_ABMain(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_Proofs_Reduction(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_ABSpecEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_ABMain(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
