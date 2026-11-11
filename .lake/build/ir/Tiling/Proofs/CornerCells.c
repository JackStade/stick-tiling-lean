// Lean compiler output
// Module: Tiling.Proofs.CornerCells
// Imports: public import Init public meta import Init public import Mathlib.Tactic.Module public import Tiling.Proofs.StackedPairs
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
lean_object* lp_Tiling_StickPolyhex_nbr(lean_object*, lean_object*);
lean_object* l_Int_instDecidableEq___boxed(lean_object*, lean_object*);
uint8_t l_instDecidableEqProd___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_StickTiling_stickOf(lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Multiset_decidableMem___aux__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* lp_Tiling_Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_Tiling_StickPolyhex_StickTiling_cornerCells___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_cornerCells___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_cornerCells___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_cornerCells___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_Tiling_StickPolyhex_StickTiling_cornerCells___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_cornerCells___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_Tiling_StickPolyhex_StickTiling_cornerCells___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Tiling_StickPolyhex_StickTiling_cornerCells___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Tiling_StickPolyhex_StickTiling_cornerCells___closed__0 = (const lean_object*)&lp_Tiling_StickPolyhex_StickTiling_cornerCells___closed__0_value;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_cornerCells(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_Tiling_StickPolyhex_StickTiling_cornerCells___lam__0(lean_object* v_a_1_, lean_object* v_b_2_){
_start:
{
lean_object* v___x_3_; uint8_t v___x_4_; 
v___x_3_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
lean_inc_ref(v___x_3_);
v___x_4_ = l_instDecidableEqProd___redArg(v___x_3_, v___x_3_, v_a_1_, v_b_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_cornerCells___lam__0___boxed(lean_object* v_a_5_, lean_object* v_b_6_){
_start:
{
uint8_t v_res_7_; lean_object* v_r_8_; 
v_res_7_ = lp_Tiling_StickPolyhex_StickTiling_cornerCells___lam__0(v_a_5_, v_b_6_);
v_r_8_ = lean_box(v_res_7_);
return v_r_8_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_cornerCells___lam__1(lean_object* v_g_9_, lean_object* v_x_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lp_Tiling_StickPolyhex_nbr(v_x_10_, v_g_9_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_cornerCells___lam__1___boxed(lean_object* v_g_12_, lean_object* v_x_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_Tiling_StickPolyhex_StickTiling_cornerCells___lam__1(v_g_12_, v_x_13_);
lean_dec_ref(v_x_13_);
lean_dec(v_g_12_);
return v_res_14_;
}
}
LEAN_EXPORT uint8_t lp_Tiling_StickPolyhex_StickTiling_cornerCells___lam__2(lean_object* v_T_15_, lean_object* v_c_16_, lean_object* v_n_17_, lean_object* v___f_18_, lean_object* v_a_19_){
_start:
{
lean_object* v_dir_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; uint8_t v___x_24_; 
v_dir_20_ = lean_ctor_get(v_T_15_, 0);
lean_inc_ref(v_dir_20_);
lean_inc_ref(v_c_16_);
v___x_21_ = lean_apply_1(v_dir_20_, v_c_16_);
v___x_22_ = lp_Tiling_StickPolyhex_nbr(v_a_19_, v___x_21_);
lean_dec(v___x_21_);
v___x_23_ = lp_Tiling_StickPolyhex_StickTiling_stickOf(v_n_17_, v_T_15_, v_c_16_);
v___x_24_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___f_18_, v___x_22_, v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_cornerCells___lam__2___boxed(lean_object* v_T_25_, lean_object* v_c_26_, lean_object* v_n_27_, lean_object* v___f_28_, lean_object* v_a_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = lp_Tiling_StickPolyhex_StickTiling_cornerCells___lam__2(v_T_25_, v_c_26_, v_n_27_, v___f_28_, v_a_29_);
lean_dec_ref(v_a_29_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_cornerCells(lean_object* v_n_33_, lean_object* v_T_34_, lean_object* v_c_35_, lean_object* v_g_36_){
_start:
{
lean_object* v___f_37_; lean_object* v___f_38_; lean_object* v___f_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___f_37_ = ((lean_object*)(lp_Tiling_StickPolyhex_StickTiling_cornerCells___closed__0));
v___f_38_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_StickTiling_cornerCells___lam__1___boxed), 2, 1);
lean_closure_set(v___f_38_, 0, v_g_36_);
lean_inc(v_n_33_);
lean_inc_ref(v_c_35_);
lean_inc_ref(v_T_34_);
v___f_39_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_StickTiling_cornerCells___lam__2___boxed), 5, 4);
lean_closure_set(v___f_39_, 0, v_T_34_);
lean_closure_set(v___f_39_, 1, v_c_35_);
lean_closure_set(v___f_39_, 2, v_n_33_);
lean_closure_set(v___f_39_, 3, v___f_37_);
v___x_40_ = lp_Tiling_StickPolyhex_StickTiling_stickOf(v_n_33_, v_T_34_, v_c_35_);
v___x_41_ = lp_mathlib_Multiset_filter___redArg(v___f_39_, v___x_40_);
v___x_42_ = lp_Tiling_Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0___redArg(v___f_38_, v___x_41_);
return v___x_42_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic_Module(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_StackedPairs(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_Proofs_CornerCells(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_StackedPairs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
