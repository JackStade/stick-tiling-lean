// Lean compiler output
// Module: Tiling.Proofs.ABSpecEquiv
// Imports: public import Init public meta import Init public import Tiling.Proofs.ABBucketLists
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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_dataList(lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_sN(lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_vN(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_List_mapTR_loop___at___00StickPolyhex_ABSim_abSpecData_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_List_mapTR_loop___at___00StickPolyhex_ABSim_abSpecData_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_List_mapTR_loop___at___00StickPolyhex_ABSim_abSpecData_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_List_mapTR_loop___at___00StickPolyhex_ABSim_abSpecData_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_abSpecData(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_List_mapTR_loop___at___00StickPolyhex_ABSim_abSpecData_spec__2(lean_object* v_S_1_, lean_object* v_a_2_, lean_object* v_a_3_){
_start:
{
if (lean_obj_tag(v_a_2_) == 0)
{
lean_object* v___x_4_; 
lean_dec_ref(v_S_1_);
v___x_4_ = l_List_reverse___redArg(v_a_3_);
return v___x_4_;
}
else
{
lean_object* v_head_5_; lean_object* v_tail_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_16_; 
v_head_5_ = lean_ctor_get(v_a_2_, 0);
v_tail_6_ = lean_ctor_get(v_a_2_, 1);
v_isSharedCheck_16_ = !lean_is_exclusive(v_a_2_);
if (v_isSharedCheck_16_ == 0)
{
v___x_8_ = v_a_2_;
v_isShared_9_ = v_isSharedCheck_16_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_tail_6_);
lean_inc(v_head_5_);
lean_dec(v_a_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_16_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; lean_object* v_lo_11_; lean_object* v___x_13_; 
lean_inc_ref(v_S_1_);
v___x_10_ = lp_Tiling_StickPolyhex_ABSim_dataList(v_S_1_, v_head_5_);
lean_dec(v_head_5_);
v_lo_11_ = lean_ctor_get(v___x_10_, 2);
lean_inc(v_lo_11_);
lean_dec_ref(v___x_10_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_a_3_);
lean_ctor_set(v___x_8_, 0, v_lo_11_);
v___x_13_ = v___x_8_;
goto v_reusejp_12_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v_lo_11_);
lean_ctor_set(v_reuseFailAlloc_15_, 1, v_a_3_);
v___x_13_ = v_reuseFailAlloc_15_;
goto v_reusejp_12_;
}
v_reusejp_12_:
{
v_a_2_ = v_tail_6_;
v_a_3_ = v___x_13_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_List_mapTR_loop___at___00StickPolyhex_ABSim_abSpecData_spec__0(lean_object* v_S_17_, lean_object* v_a_18_, lean_object* v_a_19_){
_start:
{
if (lean_obj_tag(v_a_18_) == 0)
{
lean_object* v___x_20_; 
lean_dec_ref(v_S_17_);
v___x_20_ = l_List_reverse___redArg(v_a_19_);
return v___x_20_;
}
else
{
lean_object* v_head_21_; lean_object* v_tail_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_32_; 
v_head_21_ = lean_ctor_get(v_a_18_, 0);
v_tail_22_ = lean_ctor_get(v_a_18_, 1);
v_isSharedCheck_32_ = !lean_is_exclusive(v_a_18_);
if (v_isSharedCheck_32_ == 0)
{
v___x_24_ = v_a_18_;
v_isShared_25_ = v_isSharedCheck_32_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_tail_22_);
lean_inc(v_head_21_);
lean_dec(v_a_18_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_32_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_26_; lean_object* v_L_27_; lean_object* v___x_29_; 
lean_inc_ref(v_S_17_);
v___x_26_ = lp_Tiling_StickPolyhex_ABSim_dataList(v_S_17_, v_head_21_);
lean_dec(v_head_21_);
v_L_27_ = lean_ctor_get(v___x_26_, 0);
lean_inc(v_L_27_);
lean_dec_ref(v___x_26_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 1, v_a_19_);
lean_ctor_set(v___x_24_, 0, v_L_27_);
v___x_29_ = v___x_24_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_L_27_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v_a_19_);
v___x_29_ = v_reuseFailAlloc_31_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
v_a_18_ = v_tail_22_;
v_a_19_ = v___x_29_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_List_mapTR_loop___at___00StickPolyhex_ABSim_abSpecData_spec__3(lean_object* v_S_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
if (lean_obj_tag(v_a_34_) == 0)
{
lean_object* v___x_36_; 
lean_dec_ref(v_S_33_);
v___x_36_ = l_List_reverse___redArg(v_a_35_);
return v___x_36_;
}
else
{
lean_object* v_head_37_; lean_object* v_tail_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_48_; 
v_head_37_ = lean_ctor_get(v_a_34_, 0);
v_tail_38_ = lean_ctor_get(v_a_34_, 1);
v_isSharedCheck_48_ = !lean_is_exclusive(v_a_34_);
if (v_isSharedCheck_48_ == 0)
{
v___x_40_ = v_a_34_;
v_isShared_41_ = v_isSharedCheck_48_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_tail_38_);
lean_inc(v_head_37_);
lean_dec(v_a_34_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_48_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_42_; lean_object* v_hi_43_; lean_object* v___x_45_; 
lean_inc_ref(v_S_33_);
v___x_42_ = lp_Tiling_StickPolyhex_ABSim_dataList(v_S_33_, v_head_37_);
lean_dec(v_head_37_);
v_hi_43_ = lean_ctor_get(v___x_42_, 3);
lean_inc(v_hi_43_);
lean_dec_ref(v___x_42_);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 1, v_a_35_);
lean_ctor_set(v___x_40_, 0, v_hi_43_);
v___x_45_ = v___x_40_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_hi_43_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v_a_35_);
v___x_45_ = v_reuseFailAlloc_47_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
v_a_34_ = v_tail_38_;
v_a_35_ = v___x_45_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_List_mapTR_loop___at___00StickPolyhex_ABSim_abSpecData_spec__1(lean_object* v_S_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
if (lean_obj_tag(v_a_50_) == 0)
{
lean_object* v___x_52_; 
lean_dec_ref(v_S_49_);
v___x_52_ = l_List_reverse___redArg(v_a_51_);
return v___x_52_;
}
else
{
lean_object* v_head_53_; lean_object* v_tail_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_64_; 
v_head_53_ = lean_ctor_get(v_a_50_, 0);
v_tail_54_ = lean_ctor_get(v_a_50_, 1);
v_isSharedCheck_64_ = !lean_is_exclusive(v_a_50_);
if (v_isSharedCheck_64_ == 0)
{
v___x_56_ = v_a_50_;
v_isShared_57_ = v_isSharedCheck_64_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_tail_54_);
lean_inc(v_head_53_);
lean_dec(v_a_50_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_64_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_58_; lean_object* v_R_59_; lean_object* v___x_61_; 
lean_inc_ref(v_S_49_);
v___x_58_ = lp_Tiling_StickPolyhex_ABSim_dataList(v_S_49_, v_head_53_);
lean_dec(v_head_53_);
v_R_59_ = lean_ctor_get(v___x_58_, 1);
lean_inc(v_R_59_);
lean_dec_ref(v___x_58_);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 1, v_a_51_);
lean_ctor_set(v___x_56_, 0, v_R_59_);
v___x_61_ = v___x_56_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v_R_59_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v_a_51_);
v___x_61_ = v_reuseFailAlloc_63_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
v_a_50_ = v_tail_54_;
v_a_51_ = v___x_61_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_abSpecData(lean_object* v_S_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_66_ = lp_Tiling_StickPolyhex_ABSim_sN(v_S_65_);
lean_inc_ref_n(v_S_65_, 4);
v___x_67_ = lp_Tiling_StickPolyhex_ABSim_vN(v_S_65_);
v___x_68_ = lean_unsigned_to_nat(1u);
v___x_69_ = lean_nat_add(v___x_66_, v___x_68_);
v___x_70_ = l_List_range(v___x_69_);
v___x_71_ = lean_box(0);
lean_inc_n(v___x_70_, 3);
v___x_72_ = lp_Tiling_List_mapTR_loop___at___00StickPolyhex_ABSim_abSpecData_spec__0(v_S_65_, v___x_70_, v___x_71_);
v___x_73_ = lp_Tiling_List_mapTR_loop___at___00StickPolyhex_ABSim_abSpecData_spec__1(v_S_65_, v___x_70_, v___x_71_);
v___x_74_ = lp_Tiling_List_mapTR_loop___at___00StickPolyhex_ABSim_abSpecData_spec__2(v_S_65_, v___x_70_, v___x_71_);
v___x_75_ = lp_Tiling_List_mapTR_loop___at___00StickPolyhex_ABSim_abSpecData_spec__3(v_S_65_, v___x_70_, v___x_71_);
v___x_76_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_76_, 0, v___x_66_);
lean_ctor_set(v___x_76_, 1, v___x_67_);
lean_ctor_set(v___x_76_, 2, v___x_72_);
lean_ctor_set(v___x_76_, 3, v___x_73_);
lean_ctor_set(v___x_76_, 4, v___x_74_);
lean_ctor_set(v___x_76_, 5, v___x_75_);
return v___x_76_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_ABBucketLists(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_Proofs_ABSpecEquiv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_ABBucketLists(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
