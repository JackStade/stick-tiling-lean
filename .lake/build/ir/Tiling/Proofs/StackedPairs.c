// Lean compiler output
// Module: Tiling.Proofs.StackedPairs
// Imports: public import Init public meta import Init public import Tiling.Proofs.ValidTilings
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
lean_object* lp_Tiling_StickPolyhex_HexDir_opp(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_StickTiling_cellOfStick___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_Tiling_StickPolyhex_instDecidableSameAxis___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_instDecidableSameAxis___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_Tiling_StickPolyhex_instDecidableSameAxis(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_instDecidableSameAxis___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_tail(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_tail___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_Tiling_StickPolyhex_instDecidableSameAxis___aux__1(lean_object* v_d_1_, lean_object* v_e_2_){
_start:
{
lean_object* v___x_3_; uint8_t v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(6u);
v___x_4_ = lp_mathlib_ZMod_decidableEq(v___x_3_, v_e_2_, v_d_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_5_ = lp_Tiling_StickPolyhex_HexDir_opp(v_d_1_);
v___x_6_ = lp_mathlib_ZMod_decidableEq(v___x_3_, v_e_2_, v___x_5_);
lean_dec(v___x_5_);
return v___x_6_;
}
else
{
lean_dec(v_d_1_);
return v___x_4_;
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_instDecidableSameAxis___aux__1___boxed(lean_object* v_d_7_, lean_object* v_e_8_){
_start:
{
uint8_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = lp_Tiling_StickPolyhex_instDecidableSameAxis___aux__1(v_d_7_, v_e_8_);
lean_dec(v_e_8_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
LEAN_EXPORT uint8_t lp_Tiling_StickPolyhex_instDecidableSameAxis(lean_object* v_d_11_, lean_object* v_e_12_){
_start:
{
uint8_t v___x_13_; 
v___x_13_ = lp_Tiling_StickPolyhex_instDecidableSameAxis___aux__1(v_d_11_, v_e_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_instDecidableSameAxis___boxed(lean_object* v_d_14_, lean_object* v_e_15_){
_start:
{
uint8_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = lp_Tiling_StickPolyhex_instDecidableSameAxis(v_d_14_, v_e_15_);
lean_dec(v_e_15_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_tail(lean_object* v_n_18_, lean_object* v_T_19_, lean_object* v_c_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_21_ = lean_unsigned_to_nat(1u);
v___x_22_ = lean_nat_sub(v_n_18_, v___x_21_);
v___x_23_ = lp_Tiling_StickPolyhex_StickTiling_cellOfStick___redArg(v_T_19_, v_c_20_, v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_tail___boxed(lean_object* v_n_24_, lean_object* v_T_25_, lean_object* v_c_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lp_Tiling_StickPolyhex_StickTiling_tail(v_n_24_, v_T_25_, v_c_26_);
lean_dec(v_n_24_);
return v_res_27_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_ValidTilings(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_Proofs_StackedPairs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_ValidTilings(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
