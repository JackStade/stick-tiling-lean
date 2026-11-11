// Lean compiler output
// Module: RequestProject.StickTiling
// Imports: public import Init public meta import Init public import RequestProject.HexGrid public import RequestProject.MainResults.StickDefinitions
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
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Int_instDecidableEq___boxed(lean_object*, lean_object*);
uint8_t l_instDecidableEqProd___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_decidableBAll___redArg(lean_object*, lean_object*);
extern lean_object* lp_RequestProject_StickPolyhex_HexDir_W;
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lp_RequestProject_StickPolyhex_HexDir_vec(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_walk(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_walk___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_RequestProject_StickPolyhex_StickTiling_head___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_StickTiling_head___redArg___closed__0;
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_head___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_head(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_head___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_cellOfStick___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_cellOfStick(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_cellOfStick___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_RequestProject___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_stickOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_rows___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_rows___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_rows___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_rows___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_RequestProject_StickPolyhex_StickTiling_rows___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_RequestProject_StickPolyhex_StickTiling_rows___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_RequestProject_StickPolyhex_StickTiling_rows___redArg___closed__0 = (const lean_object*)&lp_RequestProject_StickPolyhex_StickTiling_rows___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_rows___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_rows(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_walk(lean_object* v_c_1_, lean_object* v_d_2_, lean_object* v_k_3_){
_start:
{
lean_object* v___x_4_; lean_object* v_fst_5_; lean_object* v_snd_6_; lean_object* v_fst_7_; lean_object* v_snd_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_19_; 
v___x_4_ = lp_RequestProject_StickPolyhex_HexDir_vec(v_d_2_);
v_fst_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc(v_fst_5_);
v_snd_6_ = lean_ctor_get(v___x_4_, 1);
lean_inc(v_snd_6_);
lean_dec_ref(v___x_4_);
v_fst_7_ = lean_ctor_get(v_c_1_, 0);
v_snd_8_ = lean_ctor_get(v_c_1_, 1);
v_isSharedCheck_19_ = !lean_is_exclusive(v_c_1_);
if (v_isSharedCheck_19_ == 0)
{
v___x_10_ = v_c_1_;
v_isShared_11_ = v_isSharedCheck_19_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_snd_8_);
lean_inc(v_fst_7_);
lean_dec(v_c_1_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_19_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_17_; 
v___x_12_ = lean_int_mul(v_k_3_, v_fst_5_);
lean_dec(v_fst_5_);
v___x_13_ = lean_int_mul(v_k_3_, v_snd_6_);
lean_dec(v_snd_6_);
v___x_14_ = lean_int_add(v_fst_7_, v___x_12_);
lean_dec(v___x_12_);
lean_dec(v_fst_7_);
v___x_15_ = lean_int_add(v_snd_8_, v___x_13_);
lean_dec(v___x_13_);
lean_dec(v_snd_8_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 1, v___x_15_);
lean_ctor_set(v___x_10_, 0, v___x_14_);
v___x_17_ = v___x_10_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_14_);
lean_ctor_set(v_reuseFailAlloc_18_, 1, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_walk___boxed(lean_object* v_c_20_, lean_object* v_d_21_, lean_object* v_k_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_RequestProject_StickPolyhex_walk(v_c_20_, v_d_21_, v_k_22_);
lean_dec(v_k_22_);
lean_dec(v_d_21_);
return v_res_23_;
}
}
static lean_object* _init_lp_RequestProject_StickPolyhex_StickTiling_head___redArg___closed__0(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = lean_unsigned_to_nat(1u);
v___x_25_ = lean_nat_to_int(v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_head___redArg(lean_object* v_T_26_, lean_object* v_c_27_){
_start:
{
lean_object* v_dir_28_; lean_object* v_idx_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_dir_28_ = lean_ctor_get(v_T_26_, 0);
lean_inc_ref(v_dir_28_);
v_idx_29_ = lean_ctor_get(v_T_26_, 1);
lean_inc_ref(v_idx_29_);
lean_dec_ref(v_T_26_);
lean_inc_ref_n(v_c_27_, 2);
v___x_30_ = lean_apply_1(v_dir_28_, v_c_27_);
v___x_31_ = lean_apply_1(v_idx_29_, v_c_27_);
v___x_32_ = lean_nat_to_int(v___x_31_);
v___x_33_ = lean_obj_once(&lp_RequestProject_StickPolyhex_StickTiling_head___redArg___closed__0, &lp_RequestProject_StickPolyhex_StickTiling_head___redArg___closed__0_once, _init_lp_RequestProject_StickPolyhex_StickTiling_head___redArg___closed__0);
v___x_34_ = lean_int_sub(v___x_32_, v___x_33_);
lean_dec(v___x_32_);
v___x_35_ = lean_int_neg(v___x_34_);
lean_dec(v___x_34_);
v___x_36_ = lp_RequestProject_StickPolyhex_walk(v_c_27_, v___x_30_, v___x_35_);
lean_dec(v___x_35_);
lean_dec(v___x_30_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_head(lean_object* v_n_37_, lean_object* v_T_38_, lean_object* v_c_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lp_RequestProject_StickPolyhex_StickTiling_head___redArg(v_T_38_, v_c_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_head___boxed(lean_object* v_n_41_, lean_object* v_T_42_, lean_object* v_c_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_RequestProject_StickPolyhex_StickTiling_head(v_n_41_, v_T_42_, v_c_43_);
lean_dec(v_n_41_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_cellOfStick___redArg(lean_object* v_T_45_, lean_object* v_c_46_, lean_object* v_k_47_){
_start:
{
lean_object* v_dir_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v_dir_48_ = lean_ctor_get(v_T_45_, 0);
lean_inc_ref(v_dir_48_);
lean_inc_ref(v_c_46_);
v___x_49_ = lp_RequestProject_StickPolyhex_StickTiling_head___redArg(v_T_45_, v_c_46_);
v___x_50_ = lean_apply_1(v_dir_48_, v_c_46_);
v___x_51_ = lean_nat_to_int(v_k_47_);
v___x_52_ = lp_RequestProject_StickPolyhex_walk(v___x_49_, v___x_50_, v___x_51_);
lean_dec(v___x_51_);
lean_dec(v___x_50_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_cellOfStick(lean_object* v_n_53_, lean_object* v_T_54_, lean_object* v_c_55_, lean_object* v_k_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lp_RequestProject_StickPolyhex_StickTiling_cellOfStick___redArg(v_T_54_, v_c_55_, v_k_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_cellOfStick___boxed(lean_object* v_n_58_, lean_object* v_T_59_, lean_object* v_c_60_, lean_object* v_k_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = lp_RequestProject_StickPolyhex_StickTiling_cellOfStick(v_n_58_, v_T_59_, v_c_60_, v_k_61_);
lean_dec(v_n_58_);
return v_res_62_;
}
}
LEAN_EXPORT uint8_t lp_RequestProject___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0(lean_object* v___x_63_, uint8_t v___x_64_, lean_object* v___y_65_){
_start:
{
lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_66_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
lean_inc_ref(v___x_66_);
v___x_67_ = l_instDecidableEqProd___redArg(v___x_66_, v___x_66_, v___x_63_, v___y_65_);
if (v___x_67_ == 0)
{
uint8_t v___x_68_; 
v___x_68_ = 1;
return v___x_68_;
}
else
{
return v___x_64_;
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0___boxed(lean_object* v___x_69_, lean_object* v___x_70_, lean_object* v___y_71_){
_start:
{
uint8_t v___x_293__boxed_72_; uint8_t v_res_73_; lean_object* v_r_74_; 
v___x_293__boxed_72_ = lean_unbox(v___x_70_);
v_res_73_ = lp_RequestProject___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0(v___x_69_, v___x_293__boxed_72_, v___y_71_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_as_75_, size_t v_i_76_, size_t v_stop_77_, lean_object* v_b_78_){
_start:
{
uint8_t v___x_79_; 
v___x_79_ = lean_usize_dec_eq(v_i_76_, v_stop_77_);
if (v___x_79_ == 0)
{
size_t v___x_80_; size_t v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___f_84_; uint8_t v___x_85_; 
v___x_80_ = ((size_t)1ULL);
v___x_81_ = lean_usize_sub(v_i_76_, v___x_80_);
v___x_82_ = lean_array_uget_borrowed(v_as_75_, v___x_81_);
v___x_83_ = lean_box(v___x_79_);
lean_inc(v___x_82_);
v___f_84_ = lean_alloc_closure((void*)(lp_RequestProject___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_84_, 0, v___x_82_);
lean_closure_set(v___f_84_, 1, v___x_83_);
lean_inc(v_b_78_);
v___x_85_ = l_List_decidableBAll___redArg(v___f_84_, v_b_78_);
if (v___x_85_ == 0)
{
v_i_76_ = v___x_81_;
goto _start;
}
else
{
lean_object* v___x_87_; 
lean_inc(v___x_82_);
v___x_87_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_82_);
lean_ctor_set(v___x_87_, 1, v_b_78_);
v_i_76_ = v___x_81_;
v_b_78_ = v___x_87_;
goto _start;
}
}
else
{
return v_b_78_;
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_as_89_, lean_object* v_i_90_, lean_object* v_stop_91_, lean_object* v_b_92_){
_start:
{
size_t v_i_boxed_93_; size_t v_stop_boxed_94_; lean_object* v_res_95_; 
v_i_boxed_93_ = lean_unbox_usize(v_i_90_);
lean_dec(v_i_90_);
v_stop_boxed_94_ = lean_unbox_usize(v_stop_91_);
lean_dec(v_stop_91_);
v_res_95_ = lp_RequestProject___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(v_as_89_, v_i_boxed_93_, v_stop_boxed_94_, v_b_92_);
lean_dec_ref(v_as_89_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_init_96_, lean_object* v_l_97_){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_98_ = lean_array_mk(v_l_97_);
v___x_99_ = lean_array_get_size(v___x_98_);
v___x_100_ = lean_unsigned_to_nat(0u);
v___x_101_ = lean_nat_dec_lt(v___x_100_, v___x_99_);
if (v___x_101_ == 0)
{
lean_dec_ref(v___x_98_);
return v_init_96_;
}
else
{
size_t v___x_102_; size_t v___x_103_; lean_object* v___x_104_; 
v___x_102_ = lean_usize_of_nat(v___x_99_);
v___x_103_ = ((size_t)0ULL);
v___x_104_ = lp_RequestProject___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(v___x_98_, v___x_102_, v___x_103_, v_init_96_);
lean_dec_ref(v___x_98_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_l_105_){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_box(0);
v___x_107_ = lp_RequestProject_List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v___x_106_, v_l_105_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1(lean_object* v_s_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lp_RequestProject_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_s_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0(lean_object* v_s_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = lp_RequestProject_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_s_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0___redArg(lean_object* v_f_112_, lean_object* v_s_113_){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lp_mathlib_Multiset_map___redArg(v_f_112_, v_s_113_);
v___x_115_ = lp_RequestProject_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_stickOf(lean_object* v_n_116_, lean_object* v_T_117_, lean_object* v_c_118_){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
lean_inc(v_n_116_);
v___x_119_ = lean_alloc_closure((void*)(lp_RequestProject_StickPolyhex_StickTiling_cellOfStick___boxed), 4, 3);
lean_closure_set(v___x_119_, 0, v_n_116_);
lean_closure_set(v___x_119_, 1, v_T_117_);
lean_closure_set(v___x_119_, 2, v_c_118_);
v___x_120_ = l_List_range(v_n_116_);
v___x_121_ = lp_RequestProject_Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0___redArg(v___x_119_, v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0(lean_object* v_00_u03b1_122_, lean_object* v_f_123_, lean_object* v_s_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = lp_RequestProject_Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0___redArg(v_f_123_, v_s_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1_spec__2(lean_object* v_l_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = lp_RequestProject_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_l_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_R_128_, lean_object* v_l_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = lp_RequestProject_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00StickPolyhex_StickTiling_stickOf_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_l_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_rows___redArg___lam__0(lean_object* v_x_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = lp_RequestProject_StickPolyhex_HexDir_W;
return v___x_132_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_rows___redArg___lam__0___boxed(lean_object* v_x_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = lp_RequestProject_StickPolyhex_StickTiling_rows___redArg___lam__0(v_x_133_);
lean_dec_ref(v_x_133_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_rows___redArg___lam__1(lean_object* v_n_135_, lean_object* v_c_136_){
_start:
{
lean_object* v_fst_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v_fst_137_ = lean_ctor_get(v_c_136_, 0);
v___x_138_ = lean_int_neg(v_fst_137_);
v___x_139_ = lean_nat_to_int(v_n_135_);
v___x_140_ = lean_int_emod(v___x_138_, v___x_139_);
lean_dec(v___x_139_);
lean_dec(v___x_138_);
v___x_141_ = l_Int_toNat(v___x_140_);
lean_dec(v___x_140_);
v___x_142_ = lean_unsigned_to_nat(1u);
v___x_143_ = lean_nat_add(v___x_141_, v___x_142_);
lean_dec(v___x_141_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_rows___redArg___lam__1___boxed(lean_object* v_n_144_, lean_object* v_c_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = lp_RequestProject_StickPolyhex_StickTiling_rows___redArg___lam__1(v_n_144_, v_c_145_);
lean_dec_ref(v_c_145_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_rows___redArg(lean_object* v_n_148_){
_start:
{
lean_object* v___f_149_; lean_object* v___f_150_; lean_object* v___x_151_; 
v___f_149_ = ((lean_object*)(lp_RequestProject_StickPolyhex_StickTiling_rows___redArg___closed__0));
v___f_150_ = lean_alloc_closure((void*)(lp_RequestProject_StickPolyhex_StickTiling_rows___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_150_, 0, v_n_148_);
v___x_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_151_, 0, v___f_149_);
lean_ctor_set(v___x_151_, 1, v___f_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_StickTiling_rows(lean_object* v_n_152_, lean_object* v_hn_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = lp_RequestProject_StickPolyhex_StickTiling_rows___redArg(v_n_152_);
return v___x_154_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_HexGrid(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_MainResults_StickDefinitions(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_StickTiling(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_HexGrid(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_MainResults_StickDefinitions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
