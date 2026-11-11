// Lean compiler output
// Module: Tiling.Proofs.GapAssignment
// Imports: public import Init public meta import Init public import Tiling.Proofs.GapMain
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
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_GapSpec_lbZ(lean_object*);
static lean_once_cell_t lp_Tiling_StickPolyhex_GapAssignment_lenLz___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_GapAssignment_lenLz___closed__0;
static lean_once_cell_t lp_Tiling_StickPolyhex_GapAssignment_lenLz___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_GapAssignment_lenLz___closed__1;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapAssignment_lenLz(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapAssignment_lenRz(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapAssignment_lenz(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapAssignment_offz(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapAssignment_offz___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_Tiling_StickPolyhex_GapAssignment_lenLz___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(2u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_GapAssignment_lenLz___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(1u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapAssignment_lenLz(lean_object* v_G_5_, lean_object* v_A_6_, lean_object* v_r_7_, lean_object* v_k_8_){
_start:
{
lean_object* v_v_9_; lean_object* v_st_10_; lean_object* v_xv_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v_v_9_ = lean_ctor_get(v_G_5_, 1);
lean_inc(v_v_9_);
lean_dec_ref(v_G_5_);
v_st_10_ = lean_ctor_get(v_A_6_, 0);
lean_inc_ref(v_st_10_);
v_xv_11_ = lean_ctor_get(v_A_6_, 1);
lean_inc_ref(v_xv_11_);
lean_dec_ref(v_A_6_);
v___x_12_ = lean_obj_once(&lp_Tiling_StickPolyhex_GapAssignment_lenLz___closed__0, &lp_Tiling_StickPolyhex_GapAssignment_lenLz___closed__0_once, _init_lp_Tiling_StickPolyhex_GapAssignment_lenLz___closed__0);
v___x_13_ = lean_nat_to_int(v_v_9_);
v___x_14_ = lean_int_mul(v___x_12_, v___x_13_);
lean_dec(v___x_13_);
v___x_15_ = lean_obj_once(&lp_Tiling_StickPolyhex_GapAssignment_lenLz___closed__1, &lp_Tiling_StickPolyhex_GapAssignment_lenLz___closed__1_once, _init_lp_Tiling_StickPolyhex_GapAssignment_lenLz___closed__1);
v___x_16_ = lean_int_sub(v___x_14_, v___x_15_);
lean_dec(v___x_14_);
v___x_17_ = lean_int_sub(v_r_7_, v___x_15_);
v___x_18_ = lean_apply_1(v_st_10_, v___x_17_);
v___x_19_ = lean_nat_to_int(v___x_18_);
v___x_20_ = lean_int_sub(v___x_19_, v___x_15_);
lean_dec(v___x_19_);
v___x_21_ = lean_int_mul(v___x_16_, v___x_20_);
lean_dec(v___x_20_);
lean_dec(v___x_16_);
v___x_22_ = lean_apply_2(v_xv_11_, v_r_7_, v_k_8_);
v___x_23_ = lean_int_add(v___x_21_, v___x_22_);
lean_dec(v___x_22_);
lean_dec(v___x_21_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapAssignment_lenRz(lean_object* v_G_24_, lean_object* v_A_25_, lean_object* v_r_26_, lean_object* v_k_27_){
_start:
{
lean_object* v_s_28_; lean_object* v_v_29_; lean_object* v_st_30_; lean_object* v_yv_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v_s_28_ = lean_ctor_get(v_G_24_, 0);
lean_inc(v_s_28_);
v_v_29_ = lean_ctor_get(v_G_24_, 1);
lean_inc(v_v_29_);
lean_dec_ref(v_G_24_);
v_st_30_ = lean_ctor_get(v_A_25_, 0);
lean_inc_ref(v_st_30_);
v_yv_31_ = lean_ctor_get(v_A_25_, 2);
lean_inc_ref(v_yv_31_);
lean_dec_ref(v_A_25_);
v___x_32_ = lean_obj_once(&lp_Tiling_StickPolyhex_GapAssignment_lenLz___closed__0, &lp_Tiling_StickPolyhex_GapAssignment_lenLz___closed__0_once, _init_lp_Tiling_StickPolyhex_GapAssignment_lenLz___closed__0);
v___x_33_ = lean_nat_to_int(v_v_29_);
v___x_34_ = lean_int_mul(v___x_32_, v___x_33_);
lean_dec(v___x_33_);
v___x_35_ = lean_obj_once(&lp_Tiling_StickPolyhex_GapAssignment_lenLz___closed__1, &lp_Tiling_StickPolyhex_GapAssignment_lenLz___closed__1_once, _init_lp_Tiling_StickPolyhex_GapAssignment_lenLz___closed__1);
v___x_36_ = lean_int_sub(v___x_34_, v___x_35_);
lean_dec(v___x_34_);
v___x_37_ = lean_nat_to_int(v_s_28_);
v___x_38_ = lean_int_sub(v_r_26_, v___x_35_);
v___x_39_ = lean_apply_1(v_st_30_, v___x_38_);
v___x_40_ = lean_nat_to_int(v___x_39_);
v___x_41_ = lean_int_sub(v___x_37_, v___x_40_);
lean_dec(v___x_40_);
lean_dec(v___x_37_);
v___x_42_ = lean_int_mul(v___x_36_, v___x_41_);
lean_dec(v___x_41_);
lean_dec(v___x_36_);
v___x_43_ = lean_apply_2(v_yv_31_, v_r_26_, v_k_27_);
v___x_44_ = lean_int_add(v___x_42_, v___x_43_);
lean_dec(v___x_43_);
lean_dec(v___x_42_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapAssignment_lenz(lean_object* v_G_45_, lean_object* v_A_46_, lean_object* v_r_47_, lean_object* v_k_48_){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
lean_inc(v_k_48_);
lean_inc(v_r_47_);
lean_inc_ref(v_A_46_);
lean_inc_ref(v_G_45_);
v___x_49_ = lp_Tiling_StickPolyhex_GapAssignment_lenLz(v_G_45_, v_A_46_, v_r_47_, v_k_48_);
v___x_50_ = lp_Tiling_StickPolyhex_GapAssignment_lenRz(v_G_45_, v_A_46_, v_r_47_, v_k_48_);
v___x_51_ = lean_int_add(v___x_49_, v___x_50_);
lean_dec(v___x_50_);
lean_dec(v___x_49_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapAssignment_offz(lean_object* v_G_52_, lean_object* v_A_53_, lean_object* v_r_54_, lean_object* v_k_55_){
_start:
{
lean_object* v_st_56_; lean_object* v_yv_57_; lean_object* v_v_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v_st_56_ = lean_ctor_get(v_A_53_, 0);
lean_inc_ref(v_st_56_);
v_yv_57_ = lean_ctor_get(v_A_53_, 2);
lean_inc_ref(v_yv_57_);
lean_dec_ref(v_A_53_);
v_v_58_ = lean_ctor_get(v_G_52_, 1);
lean_inc(v_v_58_);
v___x_59_ = lean_obj_once(&lp_Tiling_StickPolyhex_GapAssignment_lenLz___closed__0, &lp_Tiling_StickPolyhex_GapAssignment_lenLz___closed__0_once, _init_lp_Tiling_StickPolyhex_GapAssignment_lenLz___closed__0);
v___x_60_ = lean_obj_once(&lp_Tiling_StickPolyhex_GapAssignment_lenLz___closed__1, &lp_Tiling_StickPolyhex_GapAssignment_lenLz___closed__1_once, _init_lp_Tiling_StickPolyhex_GapAssignment_lenLz___closed__1);
v___x_61_ = lean_int_sub(v_r_54_, v___x_60_);
lean_inc(v___x_61_);
v___x_62_ = lean_apply_1(v_st_56_, v___x_61_);
v___x_63_ = lean_nat_to_int(v___x_62_);
v___x_64_ = lean_int_sub(v___x_63_, v___x_60_);
lean_dec(v___x_63_);
v___x_65_ = lp_Tiling_StickPolyhex_GapSpec_lbZ(v_G_52_);
lean_dec_ref(v_G_52_);
v___x_66_ = lean_int_mul(v___x_64_, v___x_65_);
lean_dec(v___x_65_);
lean_dec(v___x_64_);
v___x_67_ = lean_int_add(v___x_59_, v___x_66_);
lean_dec(v___x_66_);
v___x_68_ = lean_nat_to_int(v_v_58_);
v___x_69_ = lean_int_add(v___x_67_, v___x_68_);
lean_dec(v___x_68_);
lean_dec(v___x_67_);
v___x_70_ = lean_apply_2(v_yv_57_, v___x_61_, v_k_55_);
v___x_71_ = lean_int_sub(v___x_69_, v___x_70_);
lean_dec(v___x_70_);
lean_dec(v___x_69_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_GapAssignment_offz___boxed(lean_object* v_G_72_, lean_object* v_A_73_, lean_object* v_r_74_, lean_object* v_k_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lp_Tiling_StickPolyhex_GapAssignment_offz(v_G_72_, v_A_73_, v_r_74_, v_k_75_);
lean_dec(v_r_74_);
return v_res_76_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_GapMain(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_Proofs_GapAssignment(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_GapMain(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
