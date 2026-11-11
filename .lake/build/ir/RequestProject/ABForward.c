// Lean compiler output
// Module: RequestProject.ABForward
// Imports: public import Init public meta import Init public import RequestProject.ABLineValues
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
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_cyc(lean_object*, lean_object*);
lean_object* lp_RequestProject_StickPolyhex_ABSim_ABData_pha(lean_object*, lean_object*);
lean_object* lp_RequestProject_StickPolyhex_ABSim_IndexTiling_yphase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_RequestProject_StickPolyhex_ABSim_IndexTiling_xphase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__1___closed__0;
static lean_once_cell_t lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__1___closed__1;
static lean_once_cell_t lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__1___closed__2;
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__0(lean_object* v_D_1_, lean_object* v_r_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_3_ = lean_int_neg(v_r_2_);
v___x_4_ = lp_RequestProject_StickPolyhex_ABSim_ABData_pha(v_D_1_, v___x_3_);
lean_dec(v___x_3_);
v___x_5_ = lean_unsigned_to_nat(1u);
v___x_6_ = lean_nat_add(v___x_4_, v___x_5_);
lean_dec(v___x_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__0___boxed(lean_object* v_D_7_, lean_object* v_r_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__0(v_D_7_, v_r_8_);
lean_dec(v_r_8_);
lean_dec_ref(v_D_7_);
return v_res_9_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__1___closed__0(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_unsigned_to_nat(2u);
v___x_11_ = lean_nat_to_int(v___x_10_);
return v___x_11_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__1___closed__1(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_unsigned_to_nat(0u);
v___x_13_ = lean_nat_to_int(v___x_12_);
return v___x_13_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__1___closed__2(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_unsigned_to_nat(1u);
v___x_15_ = lean_nat_to_int(v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__1(lean_object* v_D_16_, lean_object* v_T_17_, lean_object* v_J_18_, lean_object* v_r_19_){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_20_ = lean_obj_once(&lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__1___closed__0, &lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__1___closed__0_once, _init_lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__1___closed__0);
v___x_21_ = lean_int_emod(v_J_18_, v___x_20_);
v___x_22_ = lean_obj_once(&lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__1___closed__1, &lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__1___closed__1_once, _init_lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__1___closed__1);
v___x_23_ = lean_int_dec_eq(v___x_21_, v___x_22_);
lean_dec(v___x_21_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_24_ = lean_obj_once(&lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__1___closed__2, &lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__1___closed__2_once, _init_lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__1___closed__2);
v___x_25_ = lean_int_sub(v_J_18_, v___x_24_);
v___x_26_ = lean_int_ediv(v___x_25_, v___x_20_);
lean_dec(v___x_25_);
v___x_27_ = lean_int_neg(v_r_19_);
v___x_28_ = lp_RequestProject_StickPolyhex_ABSim_ABData_cyc(v_D_16_, v___x_27_);
v___x_29_ = lp_RequestProject_StickPolyhex_ABSim_ABData_pha(v_D_16_, v___x_27_);
lean_dec(v___x_27_);
v___x_30_ = lp_RequestProject_StickPolyhex_ABSim_IndexTiling_yphase(v_D_16_, v_T_17_, v___x_26_, v___x_28_, v___x_29_);
lean_dec(v___x_29_);
return v___x_30_;
}
else
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_31_ = lean_int_ediv(v_J_18_, v___x_20_);
v___x_32_ = lean_int_neg(v_r_19_);
v___x_33_ = lp_RequestProject_StickPolyhex_ABSim_ABData_cyc(v_D_16_, v___x_32_);
v___x_34_ = lp_RequestProject_StickPolyhex_ABSim_ABData_pha(v_D_16_, v___x_32_);
lean_dec(v___x_32_);
v___x_35_ = lp_RequestProject_StickPolyhex_ABSim_IndexTiling_xphase(v_D_16_, v_T_17_, v___x_31_, v___x_33_, v___x_34_);
lean_dec(v___x_34_);
return v___x_35_;
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__1___boxed(lean_object* v_D_36_, lean_object* v_T_37_, lean_object* v_J_38_, lean_object* v_r_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__1(v_D_36_, v_T_37_, v_J_38_, v_r_39_);
lean_dec(v_r_39_);
lean_dec(v_J_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex(lean_object* v_D_41_, lean_object* v_T_42_){
_start:
{
lean_object* v___f_43_; lean_object* v___f_44_; lean_object* v___x_45_; 
lean_inc_ref(v_D_41_);
v___f_43_ = lean_alloc_closure((void*)(lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__0___boxed), 2, 1);
lean_closure_set(v___f_43_, 0, v_D_41_);
v___f_44_ = lean_alloc_closure((void*)(lp_RequestProject_StickPolyhex_ABSim_IndexTiling_lineOfIndex___lam__1___boxed), 4, 2);
lean_closure_set(v___f_44_, 0, v_D_41_);
lean_closure_set(v___f_44_, 1, v_T_42_);
v___x_45_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_45_, 0, v___f_43_);
lean_ctor_set(v___x_45_, 1, v___f_44_);
return v___x_45_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_ABLineValues(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_ABForward(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_ABLineValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
