// Lean compiler output
// Module: RequestProject.Stacks
// Imports: public import Init public meta import Init public import RequestProject.StackedPairs
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
uint8_t lp_mathlib_ZMod_decidableEq(lean_object*, lean_object*, lean_object*);
lean_object* lp_RequestProject_StickPolyhex_StickTiling_head___redArg(lean_object*, lean_object*);
lean_object* lp_RequestProject_StickPolyhex_StickTiling_tail(lean_object*, lean_object*, lean_object*);
lean_object* lp_RequestProject_StickPolyhex_nbr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_endCell(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_endCell___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_frontCell(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_frontCell___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_endCell(lean_object* v_n_1_, lean_object* v_T_2_, lean_object* v_d_3_, lean_object* v_x_4_){
_start:
{
lean_object* v_dir_5_; lean_object* v___x_6_; lean_object* v___x_7_; uint8_t v___x_8_; 
v_dir_5_ = lean_ctor_get(v_T_2_, 0);
v___x_6_ = lean_unsigned_to_nat(6u);
lean_inc_ref(v_dir_5_);
lean_inc_ref(v_x_4_);
v___x_7_ = lean_apply_1(v_dir_5_, v_x_4_);
v___x_8_ = lp_mathlib_ZMod_decidableEq(v___x_6_, v___x_7_, v_d_3_);
lean_dec(v___x_7_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; 
v___x_9_ = lp_RequestProject_StickPolyhex_StickTiling_head___redArg(v_T_2_, v_x_4_);
return v___x_9_;
}
else
{
lean_object* v___x_10_; 
v___x_10_ = lp_RequestProject_StickPolyhex_StickTiling_tail(v_n_1_, v_T_2_, v_x_4_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_endCell___boxed(lean_object* v_n_11_, lean_object* v_T_12_, lean_object* v_d_13_, lean_object* v_x_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = lp_RequestProject_StickPolyhex_StickTiling_endCell(v_n_11_, v_T_12_, v_d_13_, v_x_14_);
lean_dec(v_d_13_);
lean_dec(v_n_11_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_frontCell(lean_object* v_n_16_, lean_object* v_T_17_, lean_object* v_d_18_, lean_object* v_x_19_){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lp_RequestProject_StickPolyhex_StickTiling_endCell(v_n_16_, v_T_17_, v_d_18_, v_x_19_);
v___x_21_ = lp_RequestProject_StickPolyhex_nbr(v___x_20_, v_d_18_);
lean_dec_ref(v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_frontCell___boxed(lean_object* v_n_22_, lean_object* v_T_23_, lean_object* v_d_24_, lean_object* v_x_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_RequestProject_StickPolyhex_StickTiling_frontCell(v_n_22_, v_T_23_, v_d_24_, v_x_25_);
lean_dec(v_d_24_);
lean_dec(v_n_22_);
return v_res_26_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_StackedPairs(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_Stacks(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_StackedPairs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
