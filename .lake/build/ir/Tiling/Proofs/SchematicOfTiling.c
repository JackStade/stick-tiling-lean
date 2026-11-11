// Lean compiler output
// Module: Tiling.Proofs.SchematicOfTiling
// Imports: public import Init public meta import Init public import Tiling.Proofs.WeaveAlign
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
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_shearCell(lean_object*, lean_object*);
extern lean_object* lp_Tiling_StickPolyhex_HexDir_W;
uint8_t lp_mathlib_ZMod_decidableEq(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_Tiling_StickPolyhex_HexDir_SE;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_translate___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_translate___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_translate___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_translate___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_translate___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_translate(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_translate___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_slotOfCell(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_slotOfCell___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_Tiling_StickPolyhex_StickTiling_refCell___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_StickTiling_refCell___closed__0;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_refCell(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_refCell___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_translate___redArg___lam__0(lean_object* v_T_1_, lean_object* v_v_2_, lean_object* v_c_3_){
_start:
{
lean_object* v_dir_4_; lean_object* v_fst_5_; lean_object* v_snd_6_; lean_object* v_fst_7_; lean_object* v_snd_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_18_; 
v_dir_4_ = lean_ctor_get(v_T_1_, 0);
lean_inc_ref(v_dir_4_);
lean_dec_ref(v_T_1_);
v_fst_5_ = lean_ctor_get(v_c_3_, 0);
v_snd_6_ = lean_ctor_get(v_c_3_, 1);
v_fst_7_ = lean_ctor_get(v_v_2_, 0);
v_snd_8_ = lean_ctor_get(v_v_2_, 1);
v_isSharedCheck_18_ = !lean_is_exclusive(v_v_2_);
if (v_isSharedCheck_18_ == 0)
{
v___x_10_ = v_v_2_;
v_isShared_11_ = v_isSharedCheck_18_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_snd_8_);
lean_inc(v_fst_7_);
lean_dec(v_v_2_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_18_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_15_; 
v___x_12_ = lean_int_add(v_fst_5_, v_fst_7_);
lean_dec(v_fst_7_);
v___x_13_ = lean_int_add(v_snd_6_, v_snd_8_);
lean_dec(v_snd_8_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 1, v___x_13_);
lean_ctor_set(v___x_10_, 0, v___x_12_);
v___x_15_ = v___x_10_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v___x_12_);
lean_ctor_set(v_reuseFailAlloc_17_, 1, v___x_13_);
v___x_15_ = v_reuseFailAlloc_17_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
lean_object* v___x_16_; 
v___x_16_ = lean_apply_1(v_dir_4_, v___x_15_);
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_translate___redArg___lam__0___boxed(lean_object* v_T_19_, lean_object* v_v_20_, lean_object* v_c_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_Tiling_StickPolyhex_StickTiling_translate___redArg___lam__0(v_T_19_, v_v_20_, v_c_21_);
lean_dec_ref(v_c_21_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_translate___redArg___lam__1(lean_object* v_T_23_, lean_object* v_v_24_, lean_object* v_c_25_){
_start:
{
lean_object* v_idx_26_; lean_object* v_fst_27_; lean_object* v_snd_28_; lean_object* v_fst_29_; lean_object* v_snd_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_40_; 
v_idx_26_ = lean_ctor_get(v_T_23_, 1);
lean_inc_ref(v_idx_26_);
lean_dec_ref(v_T_23_);
v_fst_27_ = lean_ctor_get(v_c_25_, 0);
v_snd_28_ = lean_ctor_get(v_c_25_, 1);
v_fst_29_ = lean_ctor_get(v_v_24_, 0);
v_snd_30_ = lean_ctor_get(v_v_24_, 1);
v_isSharedCheck_40_ = !lean_is_exclusive(v_v_24_);
if (v_isSharedCheck_40_ == 0)
{
v___x_32_ = v_v_24_;
v_isShared_33_ = v_isSharedCheck_40_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_snd_30_);
lean_inc(v_fst_29_);
lean_dec(v_v_24_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_40_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_37_; 
v___x_34_ = lean_int_add(v_fst_27_, v_fst_29_);
lean_dec(v_fst_29_);
v___x_35_ = lean_int_add(v_snd_28_, v_snd_30_);
lean_dec(v_snd_30_);
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 1, v___x_35_);
lean_ctor_set(v___x_32_, 0, v___x_34_);
v___x_37_ = v___x_32_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_34_);
lean_ctor_set(v_reuseFailAlloc_39_, 1, v___x_35_);
v___x_37_ = v_reuseFailAlloc_39_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
lean_object* v___x_38_; 
v___x_38_ = lean_apply_1(v_idx_26_, v___x_37_);
return v___x_38_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_translate___redArg___lam__1___boxed(lean_object* v_T_41_, lean_object* v_v_42_, lean_object* v_c_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_Tiling_StickPolyhex_StickTiling_translate___redArg___lam__1(v_T_41_, v_v_42_, v_c_43_);
lean_dec_ref(v_c_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_translate___redArg(lean_object* v_T_45_, lean_object* v_v_46_){
_start:
{
lean_object* v___f_47_; lean_object* v___f_48_; lean_object* v___x_49_; 
lean_inc_ref(v_v_46_);
lean_inc_ref(v_T_45_);
v___f_47_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_StickTiling_translate___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_47_, 0, v_T_45_);
lean_closure_set(v___f_47_, 1, v_v_46_);
v___f_48_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_StickTiling_translate___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_48_, 0, v_T_45_);
lean_closure_set(v___f_48_, 1, v_v_46_);
v___x_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_49_, 0, v___f_47_);
lean_ctor_set(v___x_49_, 1, v___f_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_translate(lean_object* v_n_50_, lean_object* v_T_51_, lean_object* v_v_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lp_Tiling_StickPolyhex_StickTiling_translate___redArg(v_T_51_, v_v_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_translate___boxed(lean_object* v_n_54_, lean_object* v_T_55_, lean_object* v_v_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = lp_Tiling_StickPolyhex_StickTiling_translate(v_n_54_, v_T_55_, v_v_56_);
lean_dec(v_n_54_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_slotOfCell(lean_object* v_n_58_, lean_object* v_T_59_, lean_object* v_c_60_){
_start:
{
lean_object* v_dir_61_; lean_object* v_idx_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; uint8_t v___x_66_; 
v_dir_61_ = lean_ctor_get(v_T_59_, 0);
lean_inc_ref(v_dir_61_);
v_idx_62_ = lean_ctor_get(v_T_59_, 1);
lean_inc_ref(v_idx_62_);
lean_dec_ref(v_T_59_);
v___x_63_ = lean_unsigned_to_nat(6u);
lean_inc_ref(v_c_60_);
v___x_64_ = lean_apply_1(v_dir_61_, v_c_60_);
v___x_65_ = lp_Tiling_StickPolyhex_HexDir_W;
v___x_66_ = lp_mathlib_ZMod_decidableEq(v___x_63_, v___x_64_, v___x_65_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; uint8_t v___x_68_; 
lean_dec_ref(v_idx_62_);
lean_dec_ref(v_c_60_);
v___x_67_ = lp_Tiling_StickPolyhex_HexDir_SE;
v___x_68_ = lp_mathlib_ZMod_decidableEq(v___x_63_, v___x_64_, v___x_67_);
lean_dec(v___x_64_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; 
v___x_69_ = lean_box(2);
return v___x_69_;
}
else
{
lean_object* v___x_70_; 
v___x_70_ = lean_box(1);
return v___x_70_;
}
}
else
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
lean_dec(v___x_64_);
v___x_71_ = lean_unsigned_to_nat(1u);
v___x_72_ = lean_nat_add(v_n_58_, v___x_71_);
v___x_73_ = lean_apply_1(v_idx_62_, v_c_60_);
v___x_74_ = lean_nat_sub(v___x_72_, v___x_73_);
lean_dec(v___x_73_);
lean_dec(v___x_72_);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
return v___x_75_;
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_slotOfCell___boxed(lean_object* v_n_76_, lean_object* v_T_77_, lean_object* v_c_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = lp_Tiling_StickPolyhex_StickTiling_slotOfCell(v_n_76_, v_T_77_, v_c_78_);
lean_dec(v_n_76_);
return v_res_79_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_StickTiling_refCell___closed__0(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = lean_nat_to_int(v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_refCell(lean_object* v_n_82_, lean_object* v_b_83_, lean_object* v_r_84_, lean_object* v_x_85_){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_86_ = lean_nat_to_int(v_n_82_);
v___x_87_ = lean_obj_once(&lp_Tiling_StickPolyhex_StickTiling_refCell___closed__0, &lp_Tiling_StickPolyhex_StickTiling_refCell___closed__0_once, _init_lp_Tiling_StickPolyhex_StickTiling_refCell___closed__0);
v___x_88_ = lean_int_add(v___x_86_, v___x_87_);
lean_dec(v___x_86_);
v___x_89_ = lean_int_mul(v___x_88_, v_r_84_);
lean_dec(v___x_88_);
v___x_90_ = lean_int_add(v_b_83_, v___x_89_);
lean_dec(v___x_89_);
v___x_91_ = lp_Tiling_StickPolyhex_shearCell(v_x_85_, v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_refCell___boxed(lean_object* v_n_92_, lean_object* v_b_93_, lean_object* v_r_94_, lean_object* v_x_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = lp_Tiling_StickPolyhex_StickTiling_refCell(v_n_92_, v_b_93_, v_r_94_, v_x_95_);
lean_dec(v_x_95_);
lean_dec(v_r_94_);
lean_dec(v_b_93_);
return v_res_96_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_WeaveAlign(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_Proofs_SchematicOfTiling(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_WeaveAlign(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
