// Lean compiler output
// Module: RequestProject.WeaveAlign
// Imports: public import Init public meta import Init public import RequestProject.WeaveFlanks public import RequestProject.WeaveSlant
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
extern lean_object* lp_RequestProject_StickPolyhex_HexDir_W;
uint8_t lp_mathlib_ZMod_decidableEq(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_RequestProject_StickPolyhex_HexDir_NW;
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lp_RequestProject_StickPolyhex_StickTiling_flank(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_RequestProject_StickPolyhex_StickTiling_phi___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_StickTiling_phi___closed__0;
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_phi(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_bandBase(lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_RequestProject_StickPolyhex_StickTiling_phi___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_phi(lean_object* v_n_3_, lean_object* v_T_4_, lean_object* v_c_5_){
_start:
{
lean_object* v_dir_6_; lean_object* v_idx_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; uint8_t v___x_11_; 
v_dir_6_ = lean_ctor_get(v_T_4_, 0);
v_idx_7_ = lean_ctor_get(v_T_4_, 1);
lean_inc_ref(v_idx_7_);
v___x_8_ = lean_unsigned_to_nat(6u);
lean_inc_ref(v_dir_6_);
lean_inc_ref(v_c_5_);
v___x_9_ = lean_apply_1(v_dir_6_, v_c_5_);
v___x_10_ = lp_RequestProject_StickPolyhex_HexDir_W;
v___x_11_ = lp_mathlib_ZMod_decidableEq(v___x_8_, v___x_9_, v___x_10_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; uint8_t v___x_13_; 
lean_dec_ref(v_T_4_);
v___x_12_ = lp_RequestProject_StickPolyhex_HexDir_NW;
v___x_13_ = lp_mathlib_ZMod_decidableEq(v___x_8_, v___x_9_, v___x_12_);
lean_dec(v___x_9_);
if (v___x_13_ == 0)
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_14_ = lean_nat_to_int(v_n_3_);
v___x_15_ = lean_apply_1(v_idx_7_, v_c_5_);
v___x_16_ = lean_nat_to_int(v___x_15_);
v___x_17_ = lean_int_sub(v___x_14_, v___x_16_);
lean_dec(v___x_16_);
lean_dec(v___x_14_);
return v___x_17_;
}
else
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
lean_dec(v_n_3_);
v___x_18_ = lean_apply_1(v_idx_7_, v_c_5_);
v___x_19_ = lean_nat_to_int(v___x_18_);
v___x_20_ = lean_obj_once(&lp_RequestProject_StickPolyhex_StickTiling_phi___closed__0, &lp_RequestProject_StickPolyhex_StickTiling_phi___closed__0_once, _init_lp_RequestProject_StickPolyhex_StickTiling_phi___closed__0);
v___x_21_ = lean_int_sub(v___x_19_, v___x_20_);
lean_dec(v___x_19_);
return v___x_21_;
}
}
else
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
lean_dec(v___x_9_);
v___x_22_ = lp_RequestProject_StickPolyhex_StickTiling_flank(v_n_3_, v_T_4_, v___x_10_, v_c_5_);
lean_dec(v_n_3_);
v___x_23_ = lean_apply_1(v_idx_7_, v___x_22_);
v___x_24_ = lean_nat_to_int(v___x_23_);
v___x_25_ = lean_obj_once(&lp_RequestProject_StickPolyhex_StickTiling_phi___closed__0, &lp_RequestProject_StickPolyhex_StickTiling_phi___closed__0_once, _init_lp_RequestProject_StickPolyhex_StickTiling_phi___closed__0);
v___x_26_ = lean_int_sub(v___x_24_, v___x_25_);
lean_dec(v___x_24_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_bandBase(lean_object* v_n_27_, lean_object* v_T_28_, lean_object* v_c_29_){
_start:
{
lean_object* v_snd_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v_snd_30_ = lean_ctor_get(v_c_29_, 1);
lean_inc(v_snd_30_);
v___x_31_ = lp_RequestProject_StickPolyhex_StickTiling_phi(v_n_27_, v_T_28_, v_c_29_);
v___x_32_ = lean_int_sub(v_snd_30_, v___x_31_);
lean_dec(v___x_31_);
lean_dec(v_snd_30_);
return v___x_32_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_WeaveFlanks(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_WeaveSlant(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_WeaveAlign(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_WeaveFlanks(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_WeaveSlant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
