// Lean compiler output
// Module: Tiling.Proofs.ABReverse
// Imports: public import Init public meta import Init public import Tiling.Proofs.ABBackward
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
lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_idx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_tz(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_jdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_Tiling_StickPolyhex_ABSim_Backward_shift___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_shift___closed__0;
static lean_once_cell_t lp_Tiling_StickPolyhex_ABSim_Backward_shift___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_shift___closed__1;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_shift(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_shift___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_ixOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_ixOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_jxOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_jxOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_indexTilingOfLine___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_indexTilingOfLine(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_Tiling_StickPolyhex_ABSim_Backward_shift___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_ABSim_Backward_shift___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(1u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_shift(lean_object* v_D_5_, lean_object* v_A_6_, lean_object* v_r_u2080_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; uint8_t v___x_11_; 
v___x_8_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_Backward_shift___closed__0, &lp_Tiling_StickPolyhex_ABSim_Backward_shift___closed__0_once, _init_lp_Tiling_StickPolyhex_ABSim_Backward_shift___closed__0);
v___x_9_ = lp_Tiling_StickPolyhex_ABSim_Backward_idx(v_D_5_, v_A_6_, v_r_u2080_7_, v___x_8_, v___x_8_);
v___x_10_ = lp_Tiling_StickPolyhex_ABSim_ABData_tz(v_D_5_);
v___x_11_ = lean_int_dec_le(v___x_9_, v___x_10_);
lean_dec(v___x_10_);
lean_dec(v___x_9_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_Backward_shift___closed__1, &lp_Tiling_StickPolyhex_ABSim_Backward_shift___closed__1_once, _init_lp_Tiling_StickPolyhex_ABSim_Backward_shift___closed__1);
return v___x_12_;
}
else
{
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_shift___boxed(lean_object* v_D_13_, lean_object* v_A_14_, lean_object* v_r_u2080_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_Tiling_StickPolyhex_ABSim_Backward_shift(v_D_13_, v_A_14_, v_r_u2080_15_);
lean_dec(v_r_u2080_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_ixOf(lean_object* v_D_17_, lean_object* v_A_18_, lean_object* v_r_u2080_19_, lean_object* v_c_20_, lean_object* v_n_21_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
lean_inc_ref(v_A_18_);
lean_inc_ref(v_D_17_);
v___x_22_ = lp_Tiling_StickPolyhex_ABSim_Backward_shift(v_D_17_, v_A_18_, v_r_u2080_19_);
v___x_23_ = lean_int_add(v_c_20_, v___x_22_);
lean_dec(v___x_22_);
v___x_24_ = lp_Tiling_StickPolyhex_ABSim_Backward_idx(v_D_17_, v_A_18_, v_r_u2080_19_, v___x_23_, v_n_21_);
lean_dec(v___x_23_);
lean_dec_ref(v_D_17_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_ixOf___boxed(lean_object* v_D_25_, lean_object* v_A_26_, lean_object* v_r_u2080_27_, lean_object* v_c_28_, lean_object* v_n_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_Tiling_StickPolyhex_ABSim_Backward_ixOf(v_D_25_, v_A_26_, v_r_u2080_27_, v_c_28_, v_n_29_);
lean_dec(v_n_29_);
lean_dec(v_c_28_);
lean_dec(v_r_u2080_27_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_jxOf(lean_object* v_D_31_, lean_object* v_A_32_, lean_object* v_r_u2080_33_, lean_object* v_c_34_, lean_object* v_n_35_){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
lean_inc_ref(v_A_32_);
lean_inc_ref(v_D_31_);
v___x_36_ = lp_Tiling_StickPolyhex_ABSim_Backward_shift(v_D_31_, v_A_32_, v_r_u2080_33_);
v___x_37_ = lean_int_add(v_c_34_, v___x_36_);
lean_dec(v___x_36_);
v___x_38_ = lp_Tiling_StickPolyhex_ABSim_Backward_jdx(v_D_31_, v_A_32_, v_r_u2080_33_, v___x_37_, v_n_35_);
lean_dec(v___x_37_);
lean_dec_ref(v_D_31_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_jxOf___boxed(lean_object* v_D_39_, lean_object* v_A_40_, lean_object* v_r_u2080_41_, lean_object* v_c_42_, lean_object* v_n_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_Tiling_StickPolyhex_ABSim_Backward_jxOf(v_D_39_, v_A_40_, v_r_u2080_41_, v_c_42_, v_n_43_);
lean_dec(v_n_43_);
lean_dec(v_c_42_);
lean_dec(v_r_u2080_41_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_indexTilingOfLine___redArg(lean_object* v_D_45_, lean_object* v_A_46_, lean_object* v_r_u2080_47_){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
lean_inc(v_r_u2080_47_);
lean_inc_ref(v_A_46_);
lean_inc_ref(v_D_45_);
v___x_48_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_ABSim_Backward_ixOf___boxed), 5, 3);
lean_closure_set(v___x_48_, 0, v_D_45_);
lean_closure_set(v___x_48_, 1, v_A_46_);
lean_closure_set(v___x_48_, 2, v_r_u2080_47_);
v___x_49_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_ABSim_Backward_jxOf___boxed), 5, 3);
lean_closure_set(v___x_49_, 0, v_D_45_);
lean_closure_set(v___x_49_, 1, v_A_46_);
lean_closure_set(v___x_49_, 2, v_r_u2080_47_);
v___x_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_48_);
lean_ctor_set(v___x_50_, 1, v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_Backward_indexTilingOfLine(lean_object* v_D_51_, lean_object* v_A_52_, lean_object* v_r_u2080_53_, lean_object* v_hr_u2080_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lp_Tiling_StickPolyhex_ABSim_Backward_indexTilingOfLine___redArg(v_D_51_, v_A_52_, v_r_u2080_53_);
return v___x_55_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_ABBackward(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_Proofs_ABReverse(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_ABBackward(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
