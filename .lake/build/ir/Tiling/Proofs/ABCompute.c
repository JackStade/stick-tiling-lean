// Lean compiler output
// Module: Tiling.Proofs.ABCompute
// Imports: public import Init public meta import Init public import Tiling.Proofs.ABSpecEquiv public import Tiling.Proofs.GapSpecCompute
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
extern lean_object* lp_mathlib_Nat_encodable;
lean_object* lp_mathlib_List_encodable___redArg(lean_object*);
lean_object* lp_mathlib_Encodable_Prod_encodable___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Encodable_ofEquiv___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_BucketData_equivTuple___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_BucketData_equivTuple___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_BucketData_equivTuple___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_BucketData_equivTuple___lam__1___boxed(lean_object*);
static const lean_closure_object lp_Tiling_StickPolyhex_ABSim_BucketData_equivTuple___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Tiling_StickPolyhex_ABSim_BucketData_equivTuple___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Tiling_StickPolyhex_ABSim_BucketData_equivTuple___closed__0 = (const lean_object*)&lp_Tiling_StickPolyhex_ABSim_BucketData_equivTuple___closed__0_value;
static const lean_closure_object lp_Tiling_StickPolyhex_ABSim_BucketData_equivTuple___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Tiling_StickPolyhex_ABSim_BucketData_equivTuple___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Tiling_StickPolyhex_ABSim_BucketData_equivTuple___closed__1 = (const lean_object*)&lp_Tiling_StickPolyhex_ABSim_BucketData_equivTuple___closed__1_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_ABSim_BucketData_equivTuple___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_Tiling_StickPolyhex_ABSim_BucketData_equivTuple___closed__0_value),((lean_object*)&lp_Tiling_StickPolyhex_ABSim_BucketData_equivTuple___closed__1_value)}};
static const lean_object* lp_Tiling_StickPolyhex_ABSim_BucketData_equivTuple___closed__2 = (const lean_object*)&lp_Tiling_StickPolyhex_ABSim_BucketData_equivTuple___closed__2_value;
LEAN_EXPORT const lean_object* lp_Tiling_StickPolyhex_ABSim_BucketData_equivTuple = (const lean_object*)&lp_Tiling_StickPolyhex_ABSim_BucketData_equivTuple___closed__2_value;
static lean_once_cell_t lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__0;
static lean_once_cell_t lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__1;
static lean_once_cell_t lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__2;
static lean_once_cell_t lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__3;
static lean_once_cell_t lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__4;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_BucketData_equivTuple___lam__0(lean_object* v_b_1_){
_start:
{
lean_object* v_L_2_; lean_object* v_R_3_; lean_object* v_lo_4_; lean_object* v_hi_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v_L_2_ = lean_ctor_get(v_b_1_, 0);
v_R_3_ = lean_ctor_get(v_b_1_, 1);
v_lo_4_ = lean_ctor_get(v_b_1_, 2);
v_hi_5_ = lean_ctor_get(v_b_1_, 3);
lean_inc(v_hi_5_);
lean_inc(v_lo_4_);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v_lo_4_);
lean_ctor_set(v___x_6_, 1, v_hi_5_);
lean_inc(v_R_3_);
v___x_7_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7_, 0, v_R_3_);
lean_ctor_set(v___x_7_, 1, v___x_6_);
lean_inc(v_L_2_);
v___x_8_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8_, 0, v_L_2_);
lean_ctor_set(v___x_8_, 1, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_BucketData_equivTuple___lam__0___boxed(lean_object* v_b_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_Tiling_StickPolyhex_ABSim_BucketData_equivTuple___lam__0(v_b_9_);
lean_dec_ref(v_b_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_BucketData_equivTuple___lam__1(lean_object* v_p_11_){
_start:
{
lean_object* v_snd_12_; lean_object* v_snd_13_; lean_object* v_fst_14_; lean_object* v_fst_15_; lean_object* v_fst_16_; lean_object* v_snd_17_; lean_object* v___x_18_; 
v_snd_12_ = lean_ctor_get(v_p_11_, 1);
v_snd_13_ = lean_ctor_get(v_snd_12_, 1);
v_fst_14_ = lean_ctor_get(v_p_11_, 0);
v_fst_15_ = lean_ctor_get(v_snd_12_, 0);
v_fst_16_ = lean_ctor_get(v_snd_13_, 0);
v_snd_17_ = lean_ctor_get(v_snd_13_, 1);
lean_inc(v_snd_17_);
lean_inc(v_fst_16_);
lean_inc(v_fst_15_);
lean_inc(v_fst_14_);
v___x_18_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_18_, 0, v_fst_14_);
lean_ctor_set(v___x_18_, 1, v_fst_15_);
lean_ctor_set(v___x_18_, 2, v_fst_16_);
lean_ctor_set(v___x_18_, 3, v_snd_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_BucketData_equivTuple___lam__1___boxed(lean_object* v_p_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_Tiling_StickPolyhex_ABSim_BucketData_equivTuple___lam__1(v_p_19_);
lean_dec_ref(v_p_19_);
return v_res_20_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__0(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = lp_mathlib_Nat_encodable;
v___x_28_ = lp_mathlib_List_encodable___redArg(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__1(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lp_mathlib_Nat_encodable;
v___x_30_ = lp_mathlib_Encodable_Prod_encodable___redArg(v___x_29_, v___x_29_);
return v___x_30_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__2(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_31_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__1, &lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__1_once, _init_lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__1);
v___x_32_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__0, &lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__0_once, _init_lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__0);
v___x_33_ = lp_mathlib_Encodable_Prod_encodable___redArg(v___x_32_, v___x_31_);
return v___x_33_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__3(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__2, &lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__2_once, _init_lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__2);
v___x_35_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__0, &lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__0_once, _init_lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__0);
v___x_36_ = lp_mathlib_Encodable_Prod_encodable___redArg(v___x_35_, v___x_34_);
return v___x_36_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__4(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_37_ = ((lean_object*)(lp_Tiling_StickPolyhex_ABSim_BucketData_equivTuple));
v___x_38_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__3, &lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__3_once, _init_lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__3);
v___x_39_ = lp_mathlib_Encodable_ofEquiv___redArg(v___x_38_, v___x_37_);
return v___x_39_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData(void){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__4, &lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__4_once, _init_lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData___closed__4);
return v___x_40_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_ABSpecEquiv(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_GapSpecCompute(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_Proofs_ABCompute(uint8_t builtin) {
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
res = initialize_Tiling_Tiling_Proofs_GapSpecCompute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData = _init_lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData();
lean_mark_persistent(lp_Tiling_StickPolyhex_ABSim_instPrimcodableBucketData);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
