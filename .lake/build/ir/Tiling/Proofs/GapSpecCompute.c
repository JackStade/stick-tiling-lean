// Lean compiler output
// Module: Tiling.Proofs.GapSpecCompute
// Imports: public import Init public meta import Init public import Tiling.Proofs.GapSpecMarks
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
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpecData_equivTuple___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpecData_equivTuple___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpecData_equivTuple___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpecData_equivTuple___lam__1___boxed(lean_object*);
static const lean_closure_object lp_Tiling_StickPolyhex_GapSpecData_equivTuple___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Tiling_StickPolyhex_GapSpecData_equivTuple___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Tiling_StickPolyhex_GapSpecData_equivTuple___closed__0 = (const lean_object*)&lp_Tiling_StickPolyhex_GapSpecData_equivTuple___closed__0_value;
static const lean_closure_object lp_Tiling_StickPolyhex_GapSpecData_equivTuple___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Tiling_StickPolyhex_GapSpecData_equivTuple___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Tiling_StickPolyhex_GapSpecData_equivTuple___closed__1 = (const lean_object*)&lp_Tiling_StickPolyhex_GapSpecData_equivTuple___closed__1_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_GapSpecData_equivTuple___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_Tiling_StickPolyhex_GapSpecData_equivTuple___closed__0_value),((lean_object*)&lp_Tiling_StickPolyhex_GapSpecData_equivTuple___closed__1_value)}};
static const lean_object* lp_Tiling_StickPolyhex_GapSpecData_equivTuple___closed__2 = (const lean_object*)&lp_Tiling_StickPolyhex_GapSpecData_equivTuple___closed__2_value;
LEAN_EXPORT const lean_object* lp_Tiling_StickPolyhex_GapSpecData_equivTuple = (const lean_object*)&lp_Tiling_StickPolyhex_GapSpecData_equivTuple___closed__2_value;
static lean_once_cell_t lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__0;
static lean_once_cell_t lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__1;
static lean_once_cell_t lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__2;
static lean_once_cell_t lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__3;
static lean_once_cell_t lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__4;
static lean_once_cell_t lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__5;
static lean_once_cell_t lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__6;
static lean_once_cell_t lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__7;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_instPrimcodableGapSpecData;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpecData_equivTuple___lam__0(lean_object* v_G_1_){
_start:
{
lean_object* v_sRaw_2_; lean_object* v_vRaw_3_; lean_object* v_Lraw_4_; lean_object* v_Rraw_5_; lean_object* v_IloRaw_6_; lean_object* v_IhiRaw_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v_sRaw_2_ = lean_ctor_get(v_G_1_, 0);
v_vRaw_3_ = lean_ctor_get(v_G_1_, 1);
v_Lraw_4_ = lean_ctor_get(v_G_1_, 2);
v_Rraw_5_ = lean_ctor_get(v_G_1_, 3);
v_IloRaw_6_ = lean_ctor_get(v_G_1_, 4);
v_IhiRaw_7_ = lean_ctor_get(v_G_1_, 5);
lean_inc(v_IhiRaw_7_);
lean_inc(v_IloRaw_6_);
v___x_8_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8_, 0, v_IloRaw_6_);
lean_ctor_set(v___x_8_, 1, v_IhiRaw_7_);
lean_inc(v_Rraw_5_);
v___x_9_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_9_, 0, v_Rraw_5_);
lean_ctor_set(v___x_9_, 1, v___x_8_);
lean_inc(v_Lraw_4_);
v___x_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_10_, 0, v_Lraw_4_);
lean_ctor_set(v___x_10_, 1, v___x_9_);
lean_inc(v_vRaw_3_);
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v_vRaw_3_);
lean_ctor_set(v___x_11_, 1, v___x_10_);
lean_inc(v_sRaw_2_);
v___x_12_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_12_, 0, v_sRaw_2_);
lean_ctor_set(v___x_12_, 1, v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpecData_equivTuple___lam__0___boxed(lean_object* v_G_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_Tiling_StickPolyhex_GapSpecData_equivTuple___lam__0(v_G_13_);
lean_dec_ref(v_G_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpecData_equivTuple___lam__1(lean_object* v_p_15_){
_start:
{
lean_object* v_snd_16_; lean_object* v_snd_17_; lean_object* v_snd_18_; lean_object* v_snd_19_; lean_object* v_fst_20_; lean_object* v_fst_21_; lean_object* v_fst_22_; lean_object* v_fst_23_; lean_object* v_fst_24_; lean_object* v_snd_25_; lean_object* v___x_26_; 
v_snd_16_ = lean_ctor_get(v_p_15_, 1);
v_snd_17_ = lean_ctor_get(v_snd_16_, 1);
v_snd_18_ = lean_ctor_get(v_snd_17_, 1);
v_snd_19_ = lean_ctor_get(v_snd_18_, 1);
v_fst_20_ = lean_ctor_get(v_p_15_, 0);
v_fst_21_ = lean_ctor_get(v_snd_16_, 0);
v_fst_22_ = lean_ctor_get(v_snd_17_, 0);
v_fst_23_ = lean_ctor_get(v_snd_18_, 0);
v_fst_24_ = lean_ctor_get(v_snd_19_, 0);
v_snd_25_ = lean_ctor_get(v_snd_19_, 1);
lean_inc(v_snd_25_);
lean_inc(v_fst_24_);
lean_inc(v_fst_23_);
lean_inc(v_fst_22_);
lean_inc(v_fst_21_);
lean_inc(v_fst_20_);
v___x_26_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_26_, 0, v_fst_20_);
lean_ctor_set(v___x_26_, 1, v_fst_21_);
lean_ctor_set(v___x_26_, 2, v_fst_22_);
lean_ctor_set(v___x_26_, 3, v_fst_23_);
lean_ctor_set(v___x_26_, 4, v_fst_24_);
lean_ctor_set(v___x_26_, 5, v_snd_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapSpecData_equivTuple___lam__1___boxed(lean_object* v_p_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_Tiling_StickPolyhex_GapSpecData_equivTuple___lam__1(v_p_27_);
lean_dec_ref(v_p_27_);
return v_res_28_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__0(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = lp_mathlib_Nat_encodable;
v___x_36_ = lp_mathlib_List_encodable___redArg(v___x_35_);
return v___x_36_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__1(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_obj_once(&lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__0, &lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__0_once, _init_lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__0);
v___x_38_ = lp_mathlib_List_encodable___redArg(v___x_37_);
return v___x_38_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__2(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = lean_obj_once(&lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__0, &lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__0_once, _init_lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__0);
v___x_40_ = lp_mathlib_Encodable_Prod_encodable___redArg(v___x_39_, v___x_39_);
return v___x_40_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__3(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_41_ = lean_obj_once(&lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__2, &lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__2_once, _init_lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__2);
v___x_42_ = lean_obj_once(&lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__1, &lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__1_once, _init_lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__1);
v___x_43_ = lp_mathlib_Encodable_Prod_encodable___redArg(v___x_42_, v___x_41_);
return v___x_43_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__4(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = lean_obj_once(&lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__3, &lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__3_once, _init_lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__3);
v___x_45_ = lean_obj_once(&lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__1, &lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__1_once, _init_lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__1);
v___x_46_ = lp_mathlib_Encodable_Prod_encodable___redArg(v___x_45_, v___x_44_);
return v___x_46_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__5(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_47_ = lean_obj_once(&lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__4, &lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__4_once, _init_lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__4);
v___x_48_ = lp_mathlib_Nat_encodable;
v___x_49_ = lp_mathlib_Encodable_Prod_encodable___redArg(v___x_48_, v___x_47_);
return v___x_49_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__6(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = lean_obj_once(&lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__5, &lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__5_once, _init_lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__5);
v___x_51_ = lp_mathlib_Nat_encodable;
v___x_52_ = lp_mathlib_Encodable_Prod_encodable___redArg(v___x_51_, v___x_50_);
return v___x_52_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__7(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = ((lean_object*)(lp_Tiling_StickPolyhex_GapSpecData_equivTuple));
v___x_54_ = lean_obj_once(&lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__6, &lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__6_once, _init_lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__6);
v___x_55_ = lp_mathlib_Encodable_ofEquiv___redArg(v___x_54_, v___x_53_);
return v___x_55_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_instPrimcodableGapSpecData(void){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lean_obj_once(&lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__7, &lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__7_once, _init_lp_Tiling_StickPolyhex_instPrimcodableGapSpecData___closed__7);
return v___x_56_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_GapSpecMarks(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_Proofs_GapSpecCompute(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_GapSpecMarks(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_Tiling_StickPolyhex_instPrimcodableGapSpecData = _init_lp_Tiling_StickPolyhex_instPrimcodableGapSpecData();
lean_mark_persistent(lp_Tiling_StickPolyhex_instPrimcodableGapSpecData);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
