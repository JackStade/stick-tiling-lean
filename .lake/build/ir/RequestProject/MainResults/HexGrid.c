// Lean compiler output
// Module: RequestProject.MainResults.HexGrid
// Imports: public import Init public meta import Init public import Mathlib.Data.ZMod.Basic public import Mathlib.Data.Fin.VecNotation
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
lean_object* lean_int_neg(lean_object*);
lean_object* lp_mathlib_ZMod_commRing(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* l_Fin_cases___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
static lean_once_cell_t lp_RequestProject_StickPolyhex_HexDir_E___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_HexDir_E___closed__0;
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_HexDir_E;
static lean_once_cell_t lp_RequestProject_StickPolyhex_HexDir_NE___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_HexDir_NE___closed__0;
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_HexDir_NE;
LEAN_EXPORT lean_object* lp_RequestProject_Nat_cast___at___00StickPolyhex_HexDir_NW_spec__0(lean_object*);
static lean_once_cell_t lp_RequestProject_StickPolyhex_HexDir_NW___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_HexDir_NW___closed__0;
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_HexDir_NW;
static lean_once_cell_t lp_RequestProject_StickPolyhex_HexDir_W___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_HexDir_W___closed__0;
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_HexDir_W;
static lean_once_cell_t lp_RequestProject_StickPolyhex_HexDir_SW___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_HexDir_SW___closed__0;
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_HexDir_SW;
static lean_once_cell_t lp_RequestProject_StickPolyhex_HexDir_SE___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_HexDir_SE___closed__0;
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_HexDir_SE;
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_HexDir_vec___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_HexDir_vec___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_HexDir_vec___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_HexDir_vec___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_RequestProject_StickPolyhex_HexDir_vec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_RequestProject_StickPolyhex_HexDir_vec___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_RequestProject_StickPolyhex_HexDir_vec___closed__0 = (const lean_object*)&lp_RequestProject_StickPolyhex_HexDir_vec___closed__0_value;
static lean_once_cell_t lp_RequestProject_StickPolyhex_HexDir_vec___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_HexDir_vec___closed__1;
static lean_once_cell_t lp_RequestProject_StickPolyhex_HexDir_vec___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_HexDir_vec___closed__2;
static lean_once_cell_t lp_RequestProject_StickPolyhex_HexDir_vec___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_HexDir_vec___closed__3;
static lean_once_cell_t lp_RequestProject_StickPolyhex_HexDir_vec___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_HexDir_vec___closed__4;
static lean_once_cell_t lp_RequestProject_StickPolyhex_HexDir_vec___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_HexDir_vec___closed__5;
static lean_once_cell_t lp_RequestProject_StickPolyhex_HexDir_vec___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_HexDir_vec___closed__6;
static lean_once_cell_t lp_RequestProject_StickPolyhex_HexDir_vec___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_HexDir_vec___closed__7;
static lean_once_cell_t lp_RequestProject_StickPolyhex_HexDir_vec___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_HexDir_vec___closed__8;
static lean_once_cell_t lp_RequestProject_StickPolyhex_HexDir_vec___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_HexDir_vec___closed__9;
static lean_once_cell_t lp_RequestProject_StickPolyhex_HexDir_vec___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_HexDir_vec___closed__10;
static lean_once_cell_t lp_RequestProject_StickPolyhex_HexDir_vec___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_HexDir_vec___closed__11;
static lean_once_cell_t lp_RequestProject_StickPolyhex_HexDir_vec___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_HexDir_vec___closed__12;
static lean_once_cell_t lp_RequestProject_StickPolyhex_HexDir_vec___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_HexDir_vec___closed__13;
static lean_once_cell_t lp_RequestProject_StickPolyhex_HexDir_vec___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_HexDir_vec___closed__14;
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_HexDir_vec(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_HexDir_vec___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_HexDir_opp(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_nbr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_nbr___boxed(lean_object*, lean_object*);
static lean_object* _init_lp_RequestProject_StickPolyhex_HexDir_E___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(6u);
v___x_2_ = lp_mathlib_ZMod_commRing(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_HexDir_E(void){
_start:
{
lean_object* v___x_3_; lean_object* v_toSemiring_4_; lean_object* v___x_5_; lean_object* v_toZero_6_; 
v___x_3_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_E___closed__0, &lp_RequestProject_StickPolyhex_HexDir_E___closed__0_once, _init_lp_RequestProject_StickPolyhex_HexDir_E___closed__0);
v_toSemiring_4_ = lean_ctor_get(v___x_3_, 0);
lean_inc_ref(v_toSemiring_4_);
v___x_5_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_4_);
v_toZero_6_ = lean_ctor_get(v___x_5_, 1);
lean_inc(v_toZero_6_);
lean_dec_ref(v___x_5_);
return v_toZero_6_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_HexDir_NE___closed__0(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_E___closed__0, &lp_RequestProject_StickPolyhex_HexDir_E___closed__0_once, _init_lp_RequestProject_StickPolyhex_HexDir_E___closed__0);
v___x_8_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v___x_7_);
return v___x_8_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_HexDir_NE(void){
_start:
{
lean_object* v___x_9_; lean_object* v_toAddMonoidWithOne_10_; lean_object* v_toOne_11_; 
v___x_9_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_NE___closed__0, &lp_RequestProject_StickPolyhex_HexDir_NE___closed__0_once, _init_lp_RequestProject_StickPolyhex_HexDir_NE___closed__0);
v_toAddMonoidWithOne_10_ = lean_ctor_get(v___x_9_, 1);
v_toOne_11_ = lean_ctor_get(v_toAddMonoidWithOne_10_, 2);
lean_inc(v_toOne_11_);
return v_toOne_11_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_Nat_cast___at___00StickPolyhex_HexDir_NW_spec__0(lean_object* v_a_12_){
_start:
{
lean_object* v___x_13_; lean_object* v_toAddMonoidWithOne_14_; lean_object* v_toNatCast_15_; lean_object* v___x_16_; 
v___x_13_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_NE___closed__0, &lp_RequestProject_StickPolyhex_HexDir_NE___closed__0_once, _init_lp_RequestProject_StickPolyhex_HexDir_NE___closed__0);
v_toAddMonoidWithOne_14_ = lean_ctor_get(v___x_13_, 1);
v_toNatCast_15_ = lean_ctor_get(v_toAddMonoidWithOne_14_, 0);
lean_inc(v_toNatCast_15_);
v___x_16_ = lean_apply_1(v_toNatCast_15_, v_a_12_);
return v___x_16_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_HexDir_NW___closed__0(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = lean_unsigned_to_nat(2u);
v___x_18_ = lp_RequestProject_Nat_cast___at___00StickPolyhex_HexDir_NW_spec__0(v___x_17_);
return v___x_18_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_HexDir_NW(void){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_NW___closed__0, &lp_RequestProject_StickPolyhex_HexDir_NW___closed__0_once, _init_lp_RequestProject_StickPolyhex_HexDir_NW___closed__0);
return v___x_19_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_HexDir_W___closed__0(void){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lean_unsigned_to_nat(3u);
v___x_21_ = lp_RequestProject_Nat_cast___at___00StickPolyhex_HexDir_NW_spec__0(v___x_20_);
return v___x_21_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_HexDir_W(void){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_W___closed__0, &lp_RequestProject_StickPolyhex_HexDir_W___closed__0_once, _init_lp_RequestProject_StickPolyhex_HexDir_W___closed__0);
return v___x_22_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_HexDir_SW___closed__0(void){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = lean_unsigned_to_nat(4u);
v___x_24_ = lp_RequestProject_Nat_cast___at___00StickPolyhex_HexDir_NW_spec__0(v___x_23_);
return v___x_24_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_HexDir_SW(void){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_SW___closed__0, &lp_RequestProject_StickPolyhex_HexDir_SW___closed__0_once, _init_lp_RequestProject_StickPolyhex_HexDir_SW___closed__0);
return v___x_25_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_HexDir_SE___closed__0(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_unsigned_to_nat(5u);
v___x_27_ = lp_RequestProject_Nat_cast___at___00StickPolyhex_HexDir_NW_spec__0(v___x_26_);
return v___x_27_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_HexDir_SE(void){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_SE___closed__0, &lp_RequestProject_StickPolyhex_HexDir_SE___closed__0_once, _init_lp_RequestProject_StickPolyhex_HexDir_SE___closed__0);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_HexDir_vec___lam__0(lean_object* v___y_29_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_HexDir_vec___lam__0___boxed(lean_object* v___y_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_RequestProject_StickPolyhex_HexDir_vec___lam__0(v___y_30_);
lean_dec(v___y_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_HexDir_vec___lam__1(lean_object* v___x_32_, lean_object* v___f_33_, lean_object* v___y_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Fin_cases___redArg(v___x_32_, v___f_33_, v___y_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_HexDir_vec___lam__1___boxed(lean_object* v___x_36_, lean_object* v___f_37_, lean_object* v___y_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_RequestProject_StickPolyhex_HexDir_vec___lam__1(v___x_36_, v___f_37_, v___y_38_);
lean_dec(v___y_38_);
lean_dec_ref(v___x_36_);
return v_res_39_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__1(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_unsigned_to_nat(1u);
v___x_42_ = lean_nat_to_int(v___x_41_);
return v___x_42_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__2(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_unsigned_to_nat(0u);
v___x_44_ = lean_nat_to_int(v___x_43_);
return v___x_44_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__3(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_45_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_vec___closed__2, &lp_RequestProject_StickPolyhex_HexDir_vec___closed__2_once, _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__2);
v___x_46_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_vec___closed__1, &lp_RequestProject_StickPolyhex_HexDir_vec___closed__1_once, _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__1);
v___x_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
lean_ctor_set(v___x_47_, 1, v___x_45_);
return v___x_47_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__4(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_48_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_vec___closed__1, &lp_RequestProject_StickPolyhex_HexDir_vec___closed__1_once, _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__1);
v___x_49_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_vec___closed__2, &lp_RequestProject_StickPolyhex_HexDir_vec___closed__2_once, _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__2);
v___x_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v___x_48_);
return v___x_50_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__5(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_vec___closed__1, &lp_RequestProject_StickPolyhex_HexDir_vec___closed__1_once, _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__1);
v___x_52_ = lean_int_neg(v___x_51_);
return v___x_52_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__6(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_vec___closed__1, &lp_RequestProject_StickPolyhex_HexDir_vec___closed__1_once, _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__1);
v___x_54_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_vec___closed__5, &lp_RequestProject_StickPolyhex_HexDir_vec___closed__5_once, _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__5);
v___x_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v___x_53_);
return v___x_55_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__7(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_vec___closed__2, &lp_RequestProject_StickPolyhex_HexDir_vec___closed__2_once, _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__2);
v___x_57_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_vec___closed__5, &lp_RequestProject_StickPolyhex_HexDir_vec___closed__5_once, _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__5);
v___x_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
lean_ctor_set(v___x_58_, 1, v___x_56_);
return v___x_58_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__8(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_vec___closed__5, &lp_RequestProject_StickPolyhex_HexDir_vec___closed__5_once, _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__5);
v___x_60_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_vec___closed__2, &lp_RequestProject_StickPolyhex_HexDir_vec___closed__2_once, _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__2);
v___x_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
lean_ctor_set(v___x_61_, 1, v___x_59_);
return v___x_61_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__9(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_vec___closed__5, &lp_RequestProject_StickPolyhex_HexDir_vec___closed__5_once, _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__5);
v___x_63_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_vec___closed__1, &lp_RequestProject_StickPolyhex_HexDir_vec___closed__1_once, _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__1);
v___x_64_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v___x_62_);
return v___x_64_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__10(void){
_start:
{
lean_object* v___f_65_; lean_object* v___x_66_; lean_object* v___f_67_; 
v___f_65_ = ((lean_object*)(lp_RequestProject_StickPolyhex_HexDir_vec___closed__0));
v___x_66_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_vec___closed__9, &lp_RequestProject_StickPolyhex_HexDir_vec___closed__9_once, _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__9);
v___f_67_ = lean_alloc_closure((void*)(lp_RequestProject_StickPolyhex_HexDir_vec___lam__1___boxed), 3, 2);
lean_closure_set(v___f_67_, 0, v___x_66_);
lean_closure_set(v___f_67_, 1, v___f_65_);
return v___f_67_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__11(void){
_start:
{
lean_object* v___f_68_; lean_object* v___x_69_; lean_object* v___f_70_; 
v___f_68_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_vec___closed__10, &lp_RequestProject_StickPolyhex_HexDir_vec___closed__10_once, _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__10);
v___x_69_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_vec___closed__8, &lp_RequestProject_StickPolyhex_HexDir_vec___closed__8_once, _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__8);
v___f_70_ = lean_alloc_closure((void*)(lp_RequestProject_StickPolyhex_HexDir_vec___lam__1___boxed), 3, 2);
lean_closure_set(v___f_70_, 0, v___x_69_);
lean_closure_set(v___f_70_, 1, v___f_68_);
return v___f_70_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__12(void){
_start:
{
lean_object* v___f_71_; lean_object* v___x_72_; lean_object* v___f_73_; 
v___f_71_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_vec___closed__11, &lp_RequestProject_StickPolyhex_HexDir_vec___closed__11_once, _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__11);
v___x_72_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_vec___closed__7, &lp_RequestProject_StickPolyhex_HexDir_vec___closed__7_once, _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__7);
v___f_73_ = lean_alloc_closure((void*)(lp_RequestProject_StickPolyhex_HexDir_vec___lam__1___boxed), 3, 2);
lean_closure_set(v___f_73_, 0, v___x_72_);
lean_closure_set(v___f_73_, 1, v___f_71_);
return v___f_73_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__13(void){
_start:
{
lean_object* v___f_74_; lean_object* v___x_75_; lean_object* v___f_76_; 
v___f_74_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_vec___closed__12, &lp_RequestProject_StickPolyhex_HexDir_vec___closed__12_once, _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__12);
v___x_75_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_vec___closed__6, &lp_RequestProject_StickPolyhex_HexDir_vec___closed__6_once, _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__6);
v___f_76_ = lean_alloc_closure((void*)(lp_RequestProject_StickPolyhex_HexDir_vec___lam__1___boxed), 3, 2);
lean_closure_set(v___f_76_, 0, v___x_75_);
lean_closure_set(v___f_76_, 1, v___f_74_);
return v___f_76_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__14(void){
_start:
{
lean_object* v___f_77_; lean_object* v___x_78_; lean_object* v___f_79_; 
v___f_77_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_vec___closed__13, &lp_RequestProject_StickPolyhex_HexDir_vec___closed__13_once, _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__13);
v___x_78_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_vec___closed__4, &lp_RequestProject_StickPolyhex_HexDir_vec___closed__4_once, _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__4);
v___f_79_ = lean_alloc_closure((void*)(lp_RequestProject_StickPolyhex_HexDir_vec___lam__1___boxed), 3, 2);
lean_closure_set(v___f_79_, 0, v___x_78_);
lean_closure_set(v___f_79_, 1, v___f_77_);
return v___f_79_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_HexDir_vec(lean_object* v_d_80_){
_start:
{
lean_object* v___x_81_; lean_object* v___f_82_; lean_object* v___x_83_; 
v___x_81_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_vec___closed__3, &lp_RequestProject_StickPolyhex_HexDir_vec___closed__3_once, _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__3);
v___f_82_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_vec___closed__14, &lp_RequestProject_StickPolyhex_HexDir_vec___closed__14_once, _init_lp_RequestProject_StickPolyhex_HexDir_vec___closed__14);
v___x_83_ = l_Fin_cases___redArg(v___x_81_, v___f_82_, v_d_80_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_HexDir_vec___boxed(lean_object* v_d_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = lp_RequestProject_StickPolyhex_HexDir_vec(v_d_84_);
lean_dec(v_d_84_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_HexDir_opp(lean_object* v_d_86_){
_start:
{
lean_object* v___x_87_; lean_object* v_toSemiring_88_; lean_object* v___x_89_; lean_object* v_toAdd_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_87_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_E___closed__0, &lp_RequestProject_StickPolyhex_HexDir_E___closed__0_once, _init_lp_RequestProject_StickPolyhex_HexDir_E___closed__0);
v_toSemiring_88_ = lean_ctor_get(v___x_87_, 0);
lean_inc_ref(v_toSemiring_88_);
v___x_89_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_88_);
v_toAdd_90_ = lean_ctor_get(v___x_89_, 1);
lean_inc(v_toAdd_90_);
lean_dec_ref(v___x_89_);
v___x_91_ = lean_obj_once(&lp_RequestProject_StickPolyhex_HexDir_W___closed__0, &lp_RequestProject_StickPolyhex_HexDir_W___closed__0_once, _init_lp_RequestProject_StickPolyhex_HexDir_W___closed__0);
v___x_92_ = lean_apply_2(v_toAdd_90_, v_d_86_, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_nbr(lean_object* v_c_93_, lean_object* v_d_94_){
_start:
{
lean_object* v_fst_95_; lean_object* v_snd_96_; lean_object* v___x_97_; lean_object* v_fst_98_; lean_object* v_snd_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_108_; 
v_fst_95_ = lean_ctor_get(v_c_93_, 0);
v_snd_96_ = lean_ctor_get(v_c_93_, 1);
v___x_97_ = lp_RequestProject_StickPolyhex_HexDir_vec(v_d_94_);
v_fst_98_ = lean_ctor_get(v___x_97_, 0);
v_snd_99_ = lean_ctor_get(v___x_97_, 1);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_108_ == 0)
{
v___x_101_ = v___x_97_;
v_isShared_102_ = v_isSharedCheck_108_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_snd_99_);
lean_inc(v_fst_98_);
lean_dec(v___x_97_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_108_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_103_ = lean_int_add(v_fst_95_, v_fst_98_);
lean_dec(v_fst_98_);
v___x_104_ = lean_int_add(v_snd_96_, v_snd_99_);
lean_dec(v_snd_99_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 1, v___x_104_);
lean_ctor_set(v___x_101_, 0, v___x_103_);
v___x_106_ = v___x_101_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_103_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v___x_104_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_nbr___boxed(lean_object* v_c_109_, lean_object* v_d_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = lp_RequestProject_StickPolyhex_nbr(v_c_109_, v_d_110_);
lean_dec(v_d_110_);
lean_dec_ref(v_c_109_);
return v_res_111_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_ZMod_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fin_VecNotation(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_MainResults_HexGrid(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_ZMod_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fin_VecNotation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_RequestProject_StickPolyhex_HexDir_E = _init_lp_RequestProject_StickPolyhex_HexDir_E();
lean_mark_persistent(lp_RequestProject_StickPolyhex_HexDir_E);
lp_RequestProject_StickPolyhex_HexDir_NE = _init_lp_RequestProject_StickPolyhex_HexDir_NE();
lean_mark_persistent(lp_RequestProject_StickPolyhex_HexDir_NE);
lp_RequestProject_StickPolyhex_HexDir_NW = _init_lp_RequestProject_StickPolyhex_HexDir_NW();
lean_mark_persistent(lp_RequestProject_StickPolyhex_HexDir_NW);
lp_RequestProject_StickPolyhex_HexDir_W = _init_lp_RequestProject_StickPolyhex_HexDir_W();
lean_mark_persistent(lp_RequestProject_StickPolyhex_HexDir_W);
lp_RequestProject_StickPolyhex_HexDir_SW = _init_lp_RequestProject_StickPolyhex_HexDir_SW();
lean_mark_persistent(lp_RequestProject_StickPolyhex_HexDir_SW);
lp_RequestProject_StickPolyhex_HexDir_SE = _init_lp_RequestProject_StickPolyhex_HexDir_SE();
lean_mark_persistent(lp_RequestProject_StickPolyhex_HexDir_SE);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
