// Lean compiler output
// Module: Tiling.Proofs.WeaveSlant
// Imports: public import Init public meta import Init public import Tiling.Proofs.WeaveShear
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
extern lean_object* lp_Tiling_StickPolyhex_HexDir_NW;
uint8_t lp_mathlib_ZMod_decidableEq(lean_object*, lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_StickTiling_head___redArg(lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_StickTiling_tail(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_botCell(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_botCell___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_topCell(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_topCell___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_botCell(lean_object* v_n_1_, lean_object* v_T_2_, lean_object* v_c_3_){
_start:
{
lean_object* v_dir_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; uint8_t v___x_8_; 
v_dir_4_ = lean_ctor_get(v_T_2_, 0);
v___x_5_ = lean_unsigned_to_nat(6u);
lean_inc_ref(v_dir_4_);
lean_inc_ref(v_c_3_);
v___x_6_ = lean_apply_1(v_dir_4_, v_c_3_);
v___x_7_ = lp_Tiling_StickPolyhex_HexDir_NW;
v___x_8_ = lp_mathlib_ZMod_decidableEq(v___x_5_, v___x_6_, v___x_7_);
lean_dec(v___x_6_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; 
v___x_9_ = lp_Tiling_StickPolyhex_StickTiling_tail(v_n_1_, v_T_2_, v_c_3_);
return v___x_9_;
}
else
{
lean_object* v___x_10_; 
v___x_10_ = lp_Tiling_StickPolyhex_StickTiling_head___redArg(v_T_2_, v_c_3_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_botCell___boxed(lean_object* v_n_11_, lean_object* v_T_12_, lean_object* v_c_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_Tiling_StickPolyhex_StickTiling_botCell(v_n_11_, v_T_12_, v_c_13_);
lean_dec(v_n_11_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_topCell(lean_object* v_n_15_, lean_object* v_T_16_, lean_object* v_c_17_){
_start:
{
lean_object* v_dir_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; uint8_t v___x_22_; 
v_dir_18_ = lean_ctor_get(v_T_16_, 0);
v___x_19_ = lean_unsigned_to_nat(6u);
lean_inc_ref(v_dir_18_);
lean_inc_ref(v_c_17_);
v___x_20_ = lean_apply_1(v_dir_18_, v_c_17_);
v___x_21_ = lp_Tiling_StickPolyhex_HexDir_NW;
v___x_22_ = lp_mathlib_ZMod_decidableEq(v___x_19_, v___x_20_, v___x_21_);
lean_dec(v___x_20_);
if (v___x_22_ == 0)
{
lean_object* v___x_23_; 
v___x_23_ = lp_Tiling_StickPolyhex_StickTiling_head___redArg(v_T_16_, v_c_17_);
return v___x_23_;
}
else
{
lean_object* v___x_24_; 
v___x_24_ = lp_Tiling_StickPolyhex_StickTiling_tail(v_n_15_, v_T_16_, v_c_17_);
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_topCell___boxed(lean_object* v_n_25_, lean_object* v_T_26_, lean_object* v_c_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_Tiling_StickPolyhex_StickTiling_topCell(v_n_25_, v_T_26_, v_c_27_);
lean_dec(v_n_25_);
return v_res_28_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_WeaveShear(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_Proofs_WeaveSlant(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_WeaveShear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
