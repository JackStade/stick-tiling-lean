// Lean compiler output
// Module: Tiling.Proofs.ABBucketLists
// Imports: public import Init public meta import Init public import Tiling.Proofs.ABValueLists
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
lean_object* lp_Tiling_StickPolyhex_ABSim_pN(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_D_u2082L(lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_EfullL(lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_vN(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_dN(lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_C_u2082L(lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_sN(lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_g_u2084N___boxed(lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_EsetL(lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_kcount(lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_RresetL(lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_AsetL(lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_RloadL(lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_g_u2083N___boxed(lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_D_u2081L(lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_C_u2081L(lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_g_u2082N___boxed(lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_g_u2081N___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_matchList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_matchList___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_freeList_u2081(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_freeList_u2081___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_freeList_u2082(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_freeList_u2082___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_dataList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_dataList___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_matchList(lean_object* v_S_1_, lean_object* v_gN_2_, lean_object* v_i_3_){
_start:
{
lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_4_ = lean_unsigned_to_nat(1u);
v___x_5_ = lean_nat_dec_eq(v_i_3_, v___x_4_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; uint8_t v___x_7_; 
lean_dec_ref(v_gN_2_);
v___x_6_ = lean_unsigned_to_nat(2u);
v___x_7_ = lean_nat_dec_eq(v_i_3_, v___x_6_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; uint8_t v___x_9_; 
v___x_8_ = lean_unsigned_to_nat(3u);
v___x_9_ = lean_nat_dec_eq(v_i_3_, v___x_8_);
if (v___x_9_ == 0)
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
lean_inc_ref_n(v_S_1_, 2);
v___x_10_ = lp_Tiling_StickPolyhex_ABSim_EsetL(v_S_1_);
v___x_11_ = lp_Tiling_StickPolyhex_ABSim_vN(v_S_1_);
v___x_12_ = lean_unsigned_to_nat(6u);
v___x_13_ = lp_Tiling_StickPolyhex_ABSim_kcount(v_S_1_);
v___x_14_ = lean_nat_mul(v___x_12_, v___x_13_);
lean_dec(v___x_13_);
v___x_15_ = lean_nat_add(v___x_11_, v___x_14_);
lean_dec(v___x_14_);
lean_inc(v___x_10_);
v___x_16_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_16_, 0, v___x_10_);
lean_ctor_set(v___x_16_, 1, v___x_10_);
lean_ctor_set(v___x_16_, 2, v___x_11_);
lean_ctor_set(v___x_16_, 3, v___x_15_);
return v___x_16_;
}
else
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
lean_inc_ref_n(v_S_1_, 3);
v___x_17_ = lp_Tiling_StickPolyhex_ABSim_EfullL(v_S_1_);
v___x_18_ = lp_Tiling_StickPolyhex_ABSim_RresetL(v_S_1_);
v___x_19_ = lp_Tiling_StickPolyhex_ABSim_vN(v_S_1_);
v___x_20_ = lean_unsigned_to_nat(6u);
v___x_21_ = lp_Tiling_StickPolyhex_ABSim_kcount(v_S_1_);
v___x_22_ = lean_nat_mul(v___x_20_, v___x_21_);
lean_dec(v___x_21_);
v___x_23_ = lean_nat_add(v___x_19_, v___x_22_);
lean_dec(v___x_22_);
v___x_24_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_24_, 0, v___x_17_);
lean_ctor_set(v___x_24_, 1, v___x_18_);
lean_ctor_set(v___x_24_, 2, v___x_19_);
lean_ctor_set(v___x_24_, 3, v___x_23_);
return v___x_24_;
}
}
else
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
lean_inc_ref_n(v_S_1_, 3);
v___x_25_ = lp_Tiling_StickPolyhex_ABSim_EsetL(v_S_1_);
v___x_26_ = lp_Tiling_StickPolyhex_ABSim_AsetL(v_S_1_);
v___x_27_ = lp_Tiling_StickPolyhex_ABSim_vN(v_S_1_);
v___x_28_ = lean_unsigned_to_nat(6u);
v___x_29_ = lp_Tiling_StickPolyhex_ABSim_kcount(v_S_1_);
v___x_30_ = lean_nat_mul(v___x_28_, v___x_29_);
lean_dec(v___x_29_);
v___x_31_ = lean_nat_add(v___x_27_, v___x_30_);
lean_dec(v___x_30_);
v___x_32_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_32_, 0, v___x_25_);
lean_ctor_set(v___x_32_, 1, v___x_26_);
lean_ctor_set(v___x_32_, 2, v___x_27_);
lean_ctor_set(v___x_32_, 3, v___x_31_);
return v___x_32_;
}
}
else
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
lean_inc_ref_n(v_S_1_, 3);
v___x_33_ = lp_Tiling_StickPolyhex_ABSim_EfullL(v_S_1_);
v___x_34_ = lp_Tiling_StickPolyhex_ABSim_RloadL(v_S_1_, v_gN_2_);
v___x_35_ = lp_Tiling_StickPolyhex_ABSim_vN(v_S_1_);
v___x_36_ = lean_unsigned_to_nat(6u);
v___x_37_ = lp_Tiling_StickPolyhex_ABSim_kcount(v_S_1_);
v___x_38_ = lean_nat_mul(v___x_36_, v___x_37_);
lean_dec(v___x_37_);
v___x_39_ = lean_nat_add(v___x_35_, v___x_38_);
lean_dec(v___x_38_);
v___x_40_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_40_, 0, v___x_33_);
lean_ctor_set(v___x_40_, 1, v___x_34_);
lean_ctor_set(v___x_40_, 2, v___x_35_);
lean_ctor_set(v___x_40_, 3, v___x_39_);
return v___x_40_;
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_matchList___boxed(lean_object* v_S_41_, lean_object* v_gN_42_, lean_object* v_i_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_Tiling_StickPolyhex_ABSim_matchList(v_S_41_, v_gN_42_, v_i_43_);
lean_dec(v_i_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_freeList_u2081(lean_object* v_S_45_, lean_object* v_i_46_){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; uint8_t v___x_50_; 
v___x_47_ = lean_unsigned_to_nat(2u);
v___x_48_ = lp_Tiling_StickPolyhex_ABSim_pN(v_S_45_);
v___x_49_ = lean_nat_mul(v___x_47_, v___x_48_);
v___x_50_ = lean_nat_dec_le(v_i_46_, v___x_49_);
if (v___x_50_ == 0)
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; uint8_t v___x_54_; 
v___x_51_ = lean_nat_sub(v_i_46_, v___x_49_);
lean_dec(v___x_49_);
v___x_52_ = lean_nat_mod(v___x_51_, v___x_47_);
v___x_53_ = lean_unsigned_to_nat(1u);
v___x_54_ = lean_nat_dec_eq(v___x_52_, v___x_53_);
lean_dec(v___x_52_);
if (v___x_54_ == 0)
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___y_58_; lean_object* v___x_61_; lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_55_ = lean_nat_shiftr(v___x_51_, v___x_53_);
lean_dec(v___x_51_);
lean_inc_ref(v_S_45_);
v___x_56_ = lp_Tiling_StickPolyhex_ABSim_D_u2081L(v_S_45_, v___x_55_);
v___x_61_ = lean_unsigned_to_nat(4u);
v___x_62_ = lean_nat_mul(v___x_61_, v___x_48_);
lean_dec(v___x_48_);
v___x_63_ = lean_nat_dec_eq(v_i_46_, v___x_62_);
lean_dec(v___x_62_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; 
lean_inc_ref(v_S_45_);
v___x_64_ = lp_Tiling_StickPolyhex_ABSim_EfullL(v_S_45_);
v___y_58_ = v___x_64_;
goto v___jp_57_;
}
else
{
lean_object* v___x_65_; 
lean_inc_ref(v_S_45_);
v___x_65_ = lp_Tiling_StickPolyhex_ABSim_EsetL(v_S_45_);
v___y_58_ = v___x_65_;
goto v___jp_57_;
}
v___jp_57_:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lp_Tiling_StickPolyhex_ABSim_vN(v_S_45_);
lean_inc(v___x_59_);
v___x_60_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_60_, 0, v___x_56_);
lean_ctor_set(v___x_60_, 1, v___y_58_);
lean_ctor_set(v___x_60_, 2, v___x_59_);
lean_ctor_set(v___x_60_, 3, v___x_59_);
return v___x_60_;
}
}
else
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
lean_dec(v___x_48_);
lean_inc_ref_n(v_S_45_, 3);
v___x_66_ = lp_Tiling_StickPolyhex_ABSim_EfullL(v_S_45_);
v___x_67_ = lean_nat_add(v___x_51_, v___x_53_);
lean_dec(v___x_51_);
v___x_68_ = lean_nat_shiftr(v___x_67_, v___x_53_);
lean_dec(v___x_67_);
v___x_69_ = lp_Tiling_StickPolyhex_ABSim_D_u2081L(v_S_45_, v___x_68_);
v___x_70_ = lp_Tiling_StickPolyhex_ABSim_vN(v_S_45_);
v___x_71_ = lean_nat_sub(v___x_70_, v___x_53_);
v___x_72_ = lp_Tiling_StickPolyhex_ABSim_dN(v_S_45_);
v___x_73_ = lean_nat_add(v___x_70_, v___x_72_);
lean_dec(v___x_72_);
lean_dec(v___x_70_);
v___x_74_ = lean_nat_sub(v___x_73_, v___x_53_);
lean_dec(v___x_73_);
v___x_75_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_75_, 0, v___x_66_);
lean_ctor_set(v___x_75_, 1, v___x_69_);
lean_ctor_set(v___x_75_, 2, v___x_71_);
lean_ctor_set(v___x_75_, 3, v___x_74_);
return v___x_75_;
}
}
else
{
lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
lean_dec(v___x_49_);
lean_dec(v___x_48_);
v___x_76_ = lean_nat_mod(v_i_46_, v___x_47_);
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = lean_nat_dec_eq(v___x_76_, v___x_77_);
lean_dec(v___x_76_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_79_ = lean_nat_shiftr(v_i_46_, v___x_77_);
lean_inc_ref_n(v_S_45_, 2);
v___x_80_ = lp_Tiling_StickPolyhex_ABSim_C_u2081L(v_S_45_, v___x_79_);
v___x_81_ = lp_Tiling_StickPolyhex_ABSim_EfullL(v_S_45_);
v___x_82_ = lp_Tiling_StickPolyhex_ABSim_vN(v_S_45_);
lean_inc(v___x_82_);
v___x_83_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_83_, 0, v___x_80_);
lean_ctor_set(v___x_83_, 1, v___x_81_);
lean_ctor_set(v___x_83_, 2, v___x_82_);
lean_ctor_set(v___x_83_, 3, v___x_82_);
return v___x_83_;
}
else
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
lean_inc_ref_n(v_S_45_, 3);
v___x_84_ = lp_Tiling_StickPolyhex_ABSim_EfullL(v_S_45_);
v___x_85_ = lean_nat_add(v_i_46_, v___x_77_);
v___x_86_ = lean_nat_shiftr(v___x_85_, v___x_77_);
lean_dec(v___x_85_);
v___x_87_ = lp_Tiling_StickPolyhex_ABSim_C_u2081L(v_S_45_, v___x_86_);
v___x_88_ = lp_Tiling_StickPolyhex_ABSim_vN(v_S_45_);
v___x_89_ = lp_Tiling_StickPolyhex_ABSim_dN(v_S_45_);
v___x_90_ = lean_nat_sub(v___x_88_, v___x_89_);
lean_dec(v___x_89_);
v___x_91_ = lean_nat_add(v___x_90_, v___x_77_);
lean_dec(v___x_90_);
v___x_92_ = lean_nat_add(v___x_88_, v___x_77_);
lean_dec(v___x_88_);
v___x_93_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_93_, 0, v___x_84_);
lean_ctor_set(v___x_93_, 1, v___x_87_);
lean_ctor_set(v___x_93_, 2, v___x_91_);
lean_ctor_set(v___x_93_, 3, v___x_92_);
return v___x_93_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_freeList_u2081___boxed(lean_object* v_S_94_, lean_object* v_i_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = lp_Tiling_StickPolyhex_ABSim_freeList_u2081(v_S_94_, v_i_95_);
lean_dec(v_i_95_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_freeList_u2082(lean_object* v_S_97_, lean_object* v_i_98_){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_99_ = lean_unsigned_to_nat(2u);
v___x_100_ = lp_Tiling_StickPolyhex_ABSim_pN(v_S_97_);
v___x_101_ = lean_nat_mul(v___x_99_, v___x_100_);
lean_dec(v___x_100_);
v___x_102_ = lean_nat_dec_le(v_i_98_, v___x_101_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_103_ = lean_nat_sub(v_i_98_, v___x_101_);
lean_dec(v___x_101_);
v___x_104_ = lean_nat_mod(v___x_103_, v___x_99_);
v___x_105_ = lean_unsigned_to_nat(1u);
v___x_106_ = lean_nat_dec_eq(v___x_104_, v___x_105_);
lean_dec(v___x_104_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_107_ = lean_nat_shiftr(v___x_103_, v___x_105_);
lean_dec(v___x_103_);
lean_inc_ref_n(v_S_97_, 2);
v___x_108_ = lp_Tiling_StickPolyhex_ABSim_D_u2082L(v_S_97_, v___x_107_);
v___x_109_ = lp_Tiling_StickPolyhex_ABSim_EfullL(v_S_97_);
v___x_110_ = lp_Tiling_StickPolyhex_ABSim_vN(v_S_97_);
lean_inc(v___x_110_);
v___x_111_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_111_, 0, v___x_108_);
lean_ctor_set(v___x_111_, 1, v___x_109_);
lean_ctor_set(v___x_111_, 2, v___x_110_);
lean_ctor_set(v___x_111_, 3, v___x_110_);
return v___x_111_;
}
else
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
lean_inc_ref_n(v_S_97_, 3);
v___x_112_ = lp_Tiling_StickPolyhex_ABSim_EfullL(v_S_97_);
v___x_113_ = lean_nat_add(v___x_103_, v___x_105_);
lean_dec(v___x_103_);
v___x_114_ = lean_nat_shiftr(v___x_113_, v___x_105_);
lean_dec(v___x_113_);
v___x_115_ = lp_Tiling_StickPolyhex_ABSim_D_u2082L(v_S_97_, v___x_114_);
v___x_116_ = lp_Tiling_StickPolyhex_ABSim_vN(v_S_97_);
v___x_117_ = lp_Tiling_StickPolyhex_ABSim_dN(v_S_97_);
v___x_118_ = lean_nat_sub(v___x_116_, v___x_117_);
lean_dec(v___x_117_);
v___x_119_ = lean_nat_add(v___x_118_, v___x_105_);
lean_dec(v___x_118_);
v___x_120_ = lean_nat_add(v___x_116_, v___x_105_);
lean_dec(v___x_116_);
v___x_121_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_121_, 0, v___x_112_);
lean_ctor_set(v___x_121_, 1, v___x_115_);
lean_ctor_set(v___x_121_, 2, v___x_119_);
lean_ctor_set(v___x_121_, 3, v___x_120_);
return v___x_121_;
}
}
else
{
lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
lean_dec(v___x_101_);
v___x_122_ = lean_nat_mod(v_i_98_, v___x_99_);
v___x_123_ = lean_unsigned_to_nat(1u);
v___x_124_ = lean_nat_dec_eq(v___x_122_, v___x_123_);
lean_dec(v___x_122_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_125_ = lean_nat_shiftr(v_i_98_, v___x_123_);
lean_inc_ref_n(v_S_97_, 2);
v___x_126_ = lp_Tiling_StickPolyhex_ABSim_C_u2082L(v_S_97_, v___x_125_);
v___x_127_ = lp_Tiling_StickPolyhex_ABSim_EfullL(v_S_97_);
v___x_128_ = lp_Tiling_StickPolyhex_ABSim_vN(v_S_97_);
lean_inc(v___x_128_);
v___x_129_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_129_, 0, v___x_126_);
lean_ctor_set(v___x_129_, 1, v___x_127_);
lean_ctor_set(v___x_129_, 2, v___x_128_);
lean_ctor_set(v___x_129_, 3, v___x_128_);
return v___x_129_;
}
else
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
lean_inc_ref_n(v_S_97_, 3);
v___x_130_ = lp_Tiling_StickPolyhex_ABSim_EfullL(v_S_97_);
v___x_131_ = lean_nat_add(v_i_98_, v___x_123_);
v___x_132_ = lean_nat_shiftr(v___x_131_, v___x_123_);
lean_dec(v___x_131_);
v___x_133_ = lp_Tiling_StickPolyhex_ABSim_C_u2082L(v_S_97_, v___x_132_);
v___x_134_ = lp_Tiling_StickPolyhex_ABSim_vN(v_S_97_);
v___x_135_ = lean_nat_sub(v___x_134_, v___x_123_);
v___x_136_ = lp_Tiling_StickPolyhex_ABSim_dN(v_S_97_);
v___x_137_ = lean_nat_add(v___x_134_, v___x_136_);
lean_dec(v___x_136_);
lean_dec(v___x_134_);
v___x_138_ = lean_nat_sub(v___x_137_, v___x_123_);
lean_dec(v___x_137_);
v___x_139_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_139_, 0, v___x_130_);
lean_ctor_set(v___x_139_, 1, v___x_133_);
lean_ctor_set(v___x_139_, 2, v___x_135_);
lean_ctor_set(v___x_139_, 3, v___x_138_);
return v___x_139_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_freeList_u2082___boxed(lean_object* v_S_140_, lean_object* v_i_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = lp_Tiling_StickPolyhex_ABSim_freeList_u2082(v_S_140_, v_i_141_);
lean_dec(v_i_141_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_dataList(lean_object* v_S_143_, lean_object* v_q_144_){
_start:
{
lean_object* v___x_145_; uint8_t v___x_146_; 
v___x_145_ = lean_unsigned_to_nat(1u);
v___x_146_ = lean_nat_dec_eq(v_q_144_, v___x_145_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_147_ = lean_unsigned_to_nat(5u);
v___x_148_ = lean_nat_dec_le(v_q_144_, v___x_147_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_149_ = lean_unsigned_to_nat(9u);
v___x_150_ = lean_nat_dec_le(v_q_144_, v___x_149_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_151_ = lean_unsigned_to_nat(4u);
v___x_152_ = lp_Tiling_StickPolyhex_ABSim_pN(v_S_143_);
v___x_153_ = lean_nat_mul(v___x_151_, v___x_152_);
lean_dec(v___x_152_);
v___x_154_ = lean_nat_add(v___x_149_, v___x_153_);
v___x_155_ = lean_nat_dec_le(v_q_144_, v___x_154_);
lean_dec(v___x_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_156_ = lean_unsigned_to_nat(13u);
v___x_157_ = lean_nat_add(v___x_156_, v___x_153_);
v___x_158_ = lean_nat_dec_le(v_q_144_, v___x_157_);
lean_dec(v___x_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_159_ = lean_unsigned_to_nat(17u);
v___x_160_ = lean_nat_add(v___x_159_, v___x_153_);
v___x_161_ = lean_nat_dec_le(v_q_144_, v___x_160_);
lean_dec(v___x_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_162_ = lp_Tiling_StickPolyhex_ABSim_sN(v_S_143_);
v___x_163_ = lean_nat_dec_le(v_q_144_, v___x_162_);
lean_dec(v___x_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
lean_dec(v___x_153_);
v___x_164_ = lean_box(0);
v___x_165_ = lp_Tiling_StickPolyhex_ABSim_vN(v_S_143_);
lean_inc(v___x_165_);
v___x_166_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set(v___x_166_, 1, v___x_164_);
lean_ctor_set(v___x_166_, 2, v___x_165_);
lean_ctor_set(v___x_166_, 3, v___x_165_);
return v___x_166_;
}
else
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = lean_nat_sub(v_q_144_, v___x_159_);
v___x_168_ = lean_nat_sub(v___x_167_, v___x_153_);
lean_dec(v___x_153_);
lean_dec(v___x_167_);
v___x_169_ = lp_Tiling_StickPolyhex_ABSim_freeList_u2082(v_S_143_, v___x_168_);
lean_dec(v___x_168_);
return v___x_169_;
}
}
else
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
lean_inc_ref(v_S_143_);
v___x_170_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_ABSim_g_u2084N___boxed), 2, 1);
lean_closure_set(v___x_170_, 0, v_S_143_);
v___x_171_ = lean_nat_sub(v_q_144_, v___x_156_);
v___x_172_ = lean_nat_sub(v___x_171_, v___x_153_);
lean_dec(v___x_153_);
lean_dec(v___x_171_);
v___x_173_ = lp_Tiling_StickPolyhex_ABSim_matchList(v_S_143_, v___x_170_, v___x_172_);
lean_dec(v___x_172_);
return v___x_173_;
}
}
else
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
lean_inc_ref(v_S_143_);
v___x_174_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_ABSim_g_u2083N___boxed), 2, 1);
lean_closure_set(v___x_174_, 0, v_S_143_);
v___x_175_ = lean_nat_sub(v_q_144_, v___x_149_);
v___x_176_ = lean_nat_sub(v___x_175_, v___x_153_);
lean_dec(v___x_153_);
lean_dec(v___x_175_);
v___x_177_ = lp_Tiling_StickPolyhex_ABSim_matchList(v_S_143_, v___x_174_, v___x_176_);
lean_dec(v___x_176_);
return v___x_177_;
}
}
else
{
lean_object* v___x_178_; lean_object* v___x_179_; 
lean_dec(v___x_153_);
v___x_178_ = lean_nat_sub(v_q_144_, v___x_149_);
v___x_179_ = lp_Tiling_StickPolyhex_ABSim_freeList_u2081(v_S_143_, v___x_178_);
lean_dec(v___x_178_);
return v___x_179_;
}
}
else
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
lean_inc_ref(v_S_143_);
v___x_180_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_ABSim_g_u2082N___boxed), 2, 1);
lean_closure_set(v___x_180_, 0, v_S_143_);
v___x_181_ = lean_nat_sub(v_q_144_, v___x_147_);
v___x_182_ = lp_Tiling_StickPolyhex_ABSim_matchList(v_S_143_, v___x_180_, v___x_181_);
lean_dec(v___x_181_);
return v___x_182_;
}
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
lean_inc_ref(v_S_143_);
v___x_183_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_ABSim_g_u2081N___boxed), 2, 1);
lean_closure_set(v___x_183_, 0, v_S_143_);
v___x_184_ = lean_nat_sub(v_q_144_, v___x_145_);
v___x_185_ = lp_Tiling_StickPolyhex_ABSim_matchList(v_S_143_, v___x_183_, v___x_184_);
lean_dec(v___x_184_);
return v___x_185_;
}
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
lean_inc_ref(v_S_143_);
v___x_186_ = lp_Tiling_StickPolyhex_ABSim_EsetL(v_S_143_);
v___x_187_ = lp_Tiling_StickPolyhex_ABSim_vN(v_S_143_);
lean_inc(v___x_187_);
lean_inc(v___x_186_);
v___x_188_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_188_, 0, v___x_186_);
lean_ctor_set(v___x_188_, 1, v___x_186_);
lean_ctor_set(v___x_188_, 2, v___x_187_);
lean_ctor_set(v___x_188_, 3, v___x_187_);
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_dataList___boxed(lean_object* v_S_189_, lean_object* v_q_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = lp_Tiling_StickPolyhex_ABSim_dataList(v_S_189_, v_q_190_);
lean_dec(v_q_190_);
return v_res_191_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_ABValueLists(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_Proofs_ABBucketLists(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_ABValueLists(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
