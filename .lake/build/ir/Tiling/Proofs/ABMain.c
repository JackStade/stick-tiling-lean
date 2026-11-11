// Lean compiler output
// Module: Tiling.Proofs.ABMain
// Imports: public import Init public meta import Init public import Tiling.Proofs.ABForward public import Tiling.Proofs.ABReverse public import Tiling.Proofs.GapRealization
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
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t lp_Tiling_StickPolyhex_ABSim_emptyGapSpec___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_ABSim_emptyGapSpec___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_emptyGapSpec___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_emptyGapSpec___lam__0___boxed(lean_object*);
static const lean_closure_object lp_Tiling_StickPolyhex_ABSim_emptyGapSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Tiling_StickPolyhex_ABSim_emptyGapSpec___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Tiling_StickPolyhex_ABSim_emptyGapSpec___closed__0 = (const lean_object*)&lp_Tiling_StickPolyhex_ABSim_emptyGapSpec___closed__0_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_ABSim_emptyGapSpec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&lp_Tiling_StickPolyhex_ABSim_emptyGapSpec___closed__0_value),((lean_object*)&lp_Tiling_StickPolyhex_ABSim_emptyGapSpec___closed__0_value)}};
static const lean_object* lp_Tiling_StickPolyhex_ABSim_emptyGapSpec___closed__1 = (const lean_object*)&lp_Tiling_StickPolyhex_ABSim_emptyGapSpec___closed__1_value;
LEAN_EXPORT const lean_object* lp_Tiling_StickPolyhex_ABSim_emptyGapSpec = (const lean_object*)&lp_Tiling_StickPolyhex_ABSim_emptyGapSpec___closed__1_value;
static lean_object* _init_lp_Tiling_StickPolyhex_ABSim_emptyGapSpec___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_emptyGapSpec___lam__0(lean_object* v_x_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_emptyGapSpec___lam__0___closed__0, &lp_Tiling_StickPolyhex_ABSim_emptyGapSpec___lam__0___closed__0_once, _init_lp_Tiling_StickPolyhex_ABSim_emptyGapSpec___lam__0___closed__0);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_emptyGapSpec___lam__0___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_Tiling_StickPolyhex_ABSim_emptyGapSpec___lam__0(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_ABForward(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_ABReverse(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_GapRealization(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_Proofs_ABMain(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_ABForward(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_ABReverse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_GapRealization(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
