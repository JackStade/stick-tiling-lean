// Lean compiler output
// Module: Tiling.Proofs.ABLineValues
// Imports: public import Init public meta import Init public import Tiling.Proofs.ABValues public import Tiling.Proofs.ABIndex
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_P(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_exp2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_comp2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_g_u2084(lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_mxv(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_g_u2083(lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_exp1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_comp1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_g_u2082(lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_g_u2081(lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_ABData_vz(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lp_Tiling_StickPolyhex_ABSim_mcorr(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_Tiling_StickPolyhex_ABSim_IndexTiling_xphase___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_ABSim_IndexTiling_xphase___closed__0;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_IndexTiling_xphase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_IndexTiling_xphase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_Tiling_StickPolyhex_ABSim_IndexTiling_cphase___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_ABSim_IndexTiling_cphase___closed__0;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_IndexTiling_cphase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_IndexTiling_cphase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_IndexTiling_yphase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_IndexTiling_yphase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_Tiling_StickPolyhex_ABSim_IndexTiling_xphase___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_IndexTiling_xphase(lean_object* v_D_3_, lean_object* v_T_4_, lean_object* v_c_5_, lean_object* v_n_6_, lean_object* v_j_7_){
_start:
{
lean_object* v___x_8_; uint8_t v___x_9_; 
v___x_8_ = lean_unsigned_to_nat(4u);
v___x_9_ = lean_nat_dec_le(v_j_7_, v___x_8_);
if (v___x_9_ == 0)
{
lean_object* v___x_10_; uint8_t v___x_11_; 
v___x_10_ = lean_unsigned_to_nat(8u);
v___x_11_ = lean_nat_dec_le(v_j_7_, v___x_10_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_12_ = lean_unsigned_to_nat(2u);
v___x_13_ = lp_Tiling_StickPolyhex_ABSim_ABData_P(v_D_3_);
v___x_14_ = lean_nat_mul(v___x_12_, v___x_13_);
v___x_15_ = lean_nat_add(v___x_10_, v___x_14_);
v___x_16_ = lean_nat_dec_le(v_j_7_, v___x_15_);
lean_dec(v___x_15_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; uint8_t v___x_19_; 
v___x_17_ = lean_nat_mul(v___x_8_, v___x_13_);
v___x_18_ = lean_nat_add(v___x_10_, v___x_17_);
v___x_19_ = lean_nat_dec_le(v_j_7_, v___x_18_);
lean_dec(v___x_18_);
if (v___x_19_ == 0)
{
lean_object* v___x_20_; lean_object* v___x_21_; uint8_t v___x_22_; 
lean_dec(v___x_14_);
v___x_20_ = lean_unsigned_to_nat(12u);
v___x_21_ = lean_nat_add(v___x_20_, v___x_17_);
v___x_22_ = lean_nat_dec_le(v_j_7_, v___x_21_);
lean_dec(v___x_21_);
if (v___x_22_ == 0)
{
lean_object* v___x_23_; lean_object* v___x_24_; uint8_t v___x_25_; 
v___x_23_ = lean_unsigned_to_nat(16u);
v___x_24_ = lean_nat_add(v___x_23_, v___x_17_);
v___x_25_ = lean_nat_dec_le(v_j_7_, v___x_24_);
lean_dec(v___x_24_);
if (v___x_25_ == 0)
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; uint8_t v___x_29_; 
v___x_26_ = lean_unsigned_to_nat(6u);
v___x_27_ = lean_nat_mul(v___x_26_, v___x_13_);
lean_dec(v___x_13_);
v___x_28_ = lean_nat_add(v___x_23_, v___x_27_);
v___x_29_ = lean_nat_dec_le(v_j_7_, v___x_28_);
lean_dec(v___x_28_);
if (v___x_29_ == 0)
{
lean_object* v_ix_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
lean_dec(v___x_17_);
v_ix_30_ = lean_ctor_get(v_T_4_, 0);
lean_inc_ref(v_ix_30_);
lean_dec_ref(v_T_4_);
v___x_31_ = lean_unsigned_to_nat(1u);
v___x_32_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_IndexTiling_xphase___closed__0, &lp_Tiling_StickPolyhex_ABSim_IndexTiling_xphase___closed__0_once, _init_lp_Tiling_StickPolyhex_ABSim_IndexTiling_xphase___closed__0);
v___x_33_ = lean_int_add(v_n_6_, v___x_32_);
lean_dec(v_n_6_);
lean_inc(v_c_5_);
v___x_34_ = lean_apply_2(v_ix_30_, v_c_5_, v___x_33_);
v___x_35_ = lean_unsigned_to_nat(15u);
v___x_36_ = lean_nat_sub(v_j_7_, v___x_35_);
v___x_37_ = lean_nat_sub(v___x_36_, v___x_27_);
lean_dec(v___x_27_);
lean_dec(v___x_36_);
v___x_38_ = lean_nat_shiftr(v___x_37_, v___x_31_);
lean_dec(v___x_37_);
v___x_39_ = lean_nat_to_int(v___x_38_);
v___x_40_ = lp_Tiling_StickPolyhex_ABSim_ABData_exp2(v_D_3_, v_c_5_, v___x_34_, v___x_39_);
lean_dec(v___x_39_);
lean_dec(v_c_5_);
return v___x_40_;
}
else
{
lean_object* v_jx_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
lean_dec(v___x_27_);
v_jx_41_ = lean_ctor_get(v_T_4_, 1);
lean_inc_ref(v_jx_41_);
lean_dec_ref(v_T_4_);
lean_inc(v_c_5_);
v___x_42_ = lean_apply_2(v_jx_41_, v_c_5_, v_n_6_);
v___x_43_ = lean_unsigned_to_nat(15u);
v___x_44_ = lean_nat_sub(v_j_7_, v___x_43_);
v___x_45_ = lean_nat_sub(v___x_44_, v___x_17_);
lean_dec(v___x_17_);
lean_dec(v___x_44_);
v___x_46_ = lean_unsigned_to_nat(1u);
v___x_47_ = lean_nat_shiftr(v___x_45_, v___x_46_);
lean_dec(v___x_45_);
v___x_48_ = lean_nat_to_int(v___x_47_);
v___x_49_ = lp_Tiling_StickPolyhex_ABSim_ABData_comp2(v_D_3_, v_c_5_, v___x_42_, v___x_48_);
lean_dec(v___x_48_);
lean_dec(v___x_42_);
lean_dec(v_c_5_);
return v___x_49_;
}
}
else
{
lean_object* v_jx_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
lean_dec(v___x_13_);
v_jx_50_ = lean_ctor_get(v_T_4_, 1);
lean_inc_ref(v_jx_50_);
lean_dec_ref(v_T_4_);
lean_inc_ref(v_D_3_);
v___x_51_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_ABSim_ABData_g_u2084), 2, 1);
lean_closure_set(v___x_51_, 0, v_D_3_);
v___x_52_ = lean_apply_2(v_jx_50_, v_c_5_, v_n_6_);
v___x_53_ = lean_nat_sub(v_j_7_, v___x_20_);
v___x_54_ = lean_nat_sub(v___x_53_, v___x_17_);
lean_dec(v___x_17_);
lean_dec(v___x_53_);
v___x_55_ = lp_Tiling_StickPolyhex_ABSim_ABData_mxv(v_D_3_, v___x_51_, v___x_52_, v___x_54_);
lean_dec(v___x_54_);
return v___x_55_;
}
}
else
{
lean_object* v_jx_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
lean_dec(v___x_13_);
v_jx_56_ = lean_ctor_get(v_T_4_, 1);
lean_inc_ref(v_jx_56_);
lean_dec_ref(v_T_4_);
lean_inc_ref(v_D_3_);
v___x_57_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_ABSim_ABData_g_u2083), 2, 1);
lean_closure_set(v___x_57_, 0, v_D_3_);
v___x_58_ = lean_apply_2(v_jx_56_, v_c_5_, v_n_6_);
v___x_59_ = lean_nat_sub(v_j_7_, v___x_10_);
v___x_60_ = lean_nat_sub(v___x_59_, v___x_17_);
lean_dec(v___x_17_);
lean_dec(v___x_59_);
v___x_61_ = lp_Tiling_StickPolyhex_ABSim_ABData_mxv(v_D_3_, v___x_57_, v___x_58_, v___x_60_);
lean_dec(v___x_60_);
return v___x_61_;
}
}
else
{
lean_object* v_jx_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec(v___x_17_);
lean_dec(v___x_13_);
v_jx_62_ = lean_ctor_get(v_T_4_, 1);
lean_inc_ref(v_jx_62_);
lean_dec_ref(v_T_4_);
lean_inc(v_c_5_);
v___x_63_ = lean_apply_2(v_jx_62_, v_c_5_, v_n_6_);
v___x_64_ = lean_unsigned_to_nat(7u);
v___x_65_ = lean_nat_sub(v_j_7_, v___x_64_);
v___x_66_ = lean_nat_sub(v___x_65_, v___x_14_);
lean_dec(v___x_14_);
lean_dec(v___x_65_);
v___x_67_ = lean_unsigned_to_nat(1u);
v___x_68_ = lean_nat_shiftr(v___x_66_, v___x_67_);
lean_dec(v___x_66_);
v___x_69_ = lean_nat_to_int(v___x_68_);
v___x_70_ = lp_Tiling_StickPolyhex_ABSim_ABData_exp1(v_D_3_, v_c_5_, v___x_63_, v___x_69_);
lean_dec(v___x_69_);
lean_dec(v_c_5_);
return v___x_70_;
}
}
else
{
lean_object* v_ix_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
lean_dec(v___x_14_);
lean_dec(v___x_13_);
v_ix_71_ = lean_ctor_get(v_T_4_, 0);
lean_inc_ref(v_ix_71_);
lean_dec_ref(v_T_4_);
lean_inc(v_c_5_);
v___x_72_ = lean_apply_2(v_ix_71_, v_c_5_, v_n_6_);
v___x_73_ = lean_unsigned_to_nat(7u);
v___x_74_ = lean_nat_sub(v_j_7_, v___x_73_);
v___x_75_ = lean_unsigned_to_nat(1u);
v___x_76_ = lean_nat_shiftr(v___x_74_, v___x_75_);
lean_dec(v___x_74_);
v___x_77_ = lean_nat_to_int(v___x_76_);
v___x_78_ = lp_Tiling_StickPolyhex_ABSim_ABData_comp1(v_D_3_, v_c_5_, v___x_72_, v___x_77_);
lean_dec(v___x_77_);
lean_dec(v___x_72_);
lean_dec(v_c_5_);
return v___x_78_;
}
}
else
{
lean_object* v_ix_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v_ix_79_ = lean_ctor_get(v_T_4_, 0);
lean_inc_ref(v_ix_79_);
lean_dec_ref(v_T_4_);
lean_inc_ref(v_D_3_);
v___x_80_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_ABSim_ABData_g_u2082), 2, 1);
lean_closure_set(v___x_80_, 0, v_D_3_);
v___x_81_ = lean_apply_2(v_ix_79_, v_c_5_, v_n_6_);
v___x_82_ = lean_nat_sub(v_j_7_, v___x_8_);
v___x_83_ = lp_Tiling_StickPolyhex_ABSim_ABData_mxv(v_D_3_, v___x_80_, v___x_81_, v___x_82_);
lean_dec(v___x_82_);
return v___x_83_;
}
}
else
{
lean_object* v_ix_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v_ix_84_ = lean_ctor_get(v_T_4_, 0);
lean_inc_ref(v_ix_84_);
lean_dec_ref(v_T_4_);
lean_inc_ref(v_D_3_);
v___x_85_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_ABSim_ABData_g_u2081), 2, 1);
lean_closure_set(v___x_85_, 0, v_D_3_);
v___x_86_ = lean_apply_2(v_ix_84_, v_c_5_, v_n_6_);
v___x_87_ = lp_Tiling_StickPolyhex_ABSim_ABData_mxv(v_D_3_, v___x_85_, v___x_86_, v_j_7_);
return v___x_87_;
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_IndexTiling_xphase___boxed(lean_object* v_D_88_, lean_object* v_T_89_, lean_object* v_c_90_, lean_object* v_n_91_, lean_object* v_j_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = lp_Tiling_StickPolyhex_ABSim_IndexTiling_xphase(v_D_88_, v_T_89_, v_c_90_, v_n_91_, v_j_92_);
lean_dec(v_j_92_);
return v_res_93_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_ABSim_IndexTiling_cphase___closed__0(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_nat_to_int(v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_IndexTiling_cphase(lean_object* v_D_96_, lean_object* v_T_97_, lean_object* v_c_98_, lean_object* v_n_99_, lean_object* v_j_100_){
_start:
{
lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_101_ = lean_unsigned_to_nat(4u);
v___x_102_ = lean_nat_dec_le(v_j_100_, v___x_101_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_103_ = lean_unsigned_to_nat(8u);
v___x_104_ = lean_nat_dec_le(v_j_100_, v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_105_ = lp_Tiling_StickPolyhex_ABSim_ABData_P(v_D_96_);
v___x_106_ = lean_nat_mul(v___x_101_, v___x_105_);
lean_dec(v___x_105_);
v___x_107_ = lean_nat_add(v___x_103_, v___x_106_);
v___x_108_ = lean_nat_dec_le(v_j_100_, v___x_107_);
lean_dec(v___x_107_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_109_ = lean_unsigned_to_nat(12u);
v___x_110_ = lean_nat_add(v___x_109_, v___x_106_);
v___x_111_ = lean_nat_dec_le(v_j_100_, v___x_110_);
lean_dec(v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_112_ = lean_unsigned_to_nat(16u);
v___x_113_ = lean_nat_add(v___x_112_, v___x_106_);
v___x_114_ = lean_nat_dec_le(v_j_100_, v___x_113_);
lean_dec(v___x_113_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; 
lean_dec(v___x_106_);
lean_dec(v_n_99_);
lean_dec(v_c_98_);
lean_dec_ref(v_T_97_);
lean_dec_ref(v_D_96_);
v___x_115_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_IndexTiling_cphase___closed__0, &lp_Tiling_StickPolyhex_ABSim_IndexTiling_cphase___closed__0_once, _init_lp_Tiling_StickPolyhex_ABSim_IndexTiling_cphase___closed__0);
return v___x_115_;
}
else
{
lean_object* v_jx_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v_jx_116_ = lean_ctor_get(v_T_97_, 1);
lean_inc_ref_n(v_jx_116_, 2);
lean_dec_ref(v_T_97_);
v___x_117_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_ABSim_ABData_g_u2084), 2, 1);
lean_closure_set(v___x_117_, 0, v_D_96_);
lean_inc(v_n_99_);
lean_inc(v_c_98_);
v___x_118_ = lean_apply_2(v_jx_116_, v_c_98_, v_n_99_);
v___x_119_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_IndexTiling_xphase___closed__0, &lp_Tiling_StickPolyhex_ABSim_IndexTiling_xphase___closed__0_once, _init_lp_Tiling_StickPolyhex_ABSim_IndexTiling_xphase___closed__0);
v___x_120_ = lean_int_add(v_c_98_, v___x_119_);
lean_dec(v_c_98_);
v___x_121_ = lean_apply_2(v_jx_116_, v___x_120_, v_n_99_);
v___x_122_ = lean_nat_sub(v_j_100_, v___x_109_);
v___x_123_ = lean_nat_sub(v___x_122_, v___x_106_);
lean_dec(v___x_106_);
lean_dec(v___x_122_);
v___x_124_ = lp_Tiling_StickPolyhex_ABSim_mcorr(v___x_117_, v___x_118_, v___x_121_, v___x_123_);
lean_dec(v___x_123_);
return v___x_124_;
}
}
else
{
lean_object* v_jx_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v_jx_125_ = lean_ctor_get(v_T_97_, 1);
lean_inc_ref_n(v_jx_125_, 2);
lean_dec_ref(v_T_97_);
v___x_126_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_ABSim_ABData_g_u2083), 2, 1);
lean_closure_set(v___x_126_, 0, v_D_96_);
lean_inc(v_n_99_);
lean_inc(v_c_98_);
v___x_127_ = lean_apply_2(v_jx_125_, v_c_98_, v_n_99_);
v___x_128_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_IndexTiling_xphase___closed__0, &lp_Tiling_StickPolyhex_ABSim_IndexTiling_xphase___closed__0_once, _init_lp_Tiling_StickPolyhex_ABSim_IndexTiling_xphase___closed__0);
v___x_129_ = lean_int_add(v_c_98_, v___x_128_);
lean_dec(v_c_98_);
v___x_130_ = lean_apply_2(v_jx_125_, v___x_129_, v_n_99_);
v___x_131_ = lean_nat_sub(v_j_100_, v___x_103_);
v___x_132_ = lean_nat_sub(v___x_131_, v___x_106_);
lean_dec(v___x_106_);
lean_dec(v___x_131_);
v___x_133_ = lp_Tiling_StickPolyhex_ABSim_mcorr(v___x_126_, v___x_127_, v___x_130_, v___x_132_);
lean_dec(v___x_132_);
return v___x_133_;
}
}
else
{
lean_object* v___x_134_; 
lean_dec(v___x_106_);
lean_dec(v_n_99_);
lean_dec(v_c_98_);
lean_dec_ref(v_T_97_);
lean_dec_ref(v_D_96_);
v___x_134_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_IndexTiling_cphase___closed__0, &lp_Tiling_StickPolyhex_ABSim_IndexTiling_cphase___closed__0_once, _init_lp_Tiling_StickPolyhex_ABSim_IndexTiling_cphase___closed__0);
return v___x_134_;
}
}
else
{
lean_object* v_ix_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v_ix_135_ = lean_ctor_get(v_T_97_, 0);
lean_inc_ref_n(v_ix_135_, 2);
lean_dec_ref(v_T_97_);
v___x_136_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_ABSim_ABData_g_u2082), 2, 1);
lean_closure_set(v___x_136_, 0, v_D_96_);
lean_inc(v_n_99_);
lean_inc(v_c_98_);
v___x_137_ = lean_apply_2(v_ix_135_, v_c_98_, v_n_99_);
v___x_138_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_IndexTiling_xphase___closed__0, &lp_Tiling_StickPolyhex_ABSim_IndexTiling_xphase___closed__0_once, _init_lp_Tiling_StickPolyhex_ABSim_IndexTiling_xphase___closed__0);
v___x_139_ = lean_int_add(v_c_98_, v___x_138_);
lean_dec(v_c_98_);
v___x_140_ = lean_apply_2(v_ix_135_, v___x_139_, v_n_99_);
v___x_141_ = lean_nat_sub(v_j_100_, v___x_101_);
v___x_142_ = lp_Tiling_StickPolyhex_ABSim_mcorr(v___x_136_, v___x_137_, v___x_140_, v___x_141_);
lean_dec(v___x_141_);
return v___x_142_;
}
}
else
{
lean_object* v_ix_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v_ix_143_ = lean_ctor_get(v_T_97_, 0);
lean_inc_ref_n(v_ix_143_, 2);
lean_dec_ref(v_T_97_);
v___x_144_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_ABSim_ABData_g_u2081), 2, 1);
lean_closure_set(v___x_144_, 0, v_D_96_);
lean_inc(v_n_99_);
lean_inc(v_c_98_);
v___x_145_ = lean_apply_2(v_ix_143_, v_c_98_, v_n_99_);
v___x_146_ = lean_obj_once(&lp_Tiling_StickPolyhex_ABSim_IndexTiling_xphase___closed__0, &lp_Tiling_StickPolyhex_ABSim_IndexTiling_xphase___closed__0_once, _init_lp_Tiling_StickPolyhex_ABSim_IndexTiling_xphase___closed__0);
v___x_147_ = lean_int_add(v_c_98_, v___x_146_);
lean_dec(v_c_98_);
v___x_148_ = lean_apply_2(v_ix_143_, v___x_147_, v_n_99_);
v___x_149_ = lp_Tiling_StickPolyhex_ABSim_mcorr(v___x_144_, v___x_145_, v___x_148_, v_j_100_);
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_IndexTiling_cphase___boxed(lean_object* v_D_150_, lean_object* v_T_151_, lean_object* v_c_152_, lean_object* v_n_153_, lean_object* v_j_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = lp_Tiling_StickPolyhex_ABSim_IndexTiling_cphase(v_D_150_, v_T_151_, v_c_152_, v_n_153_, v_j_154_);
lean_dec(v_j_154_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_IndexTiling_yphase(lean_object* v_D_156_, lean_object* v_T_157_, lean_object* v_c_158_, lean_object* v_n_159_, lean_object* v_j_160_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_161_ = lp_Tiling_StickPolyhex_ABSim_ABData_vz(v_D_156_);
lean_inc(v_n_159_);
lean_inc(v_c_158_);
lean_inc_ref(v_T_157_);
lean_inc_ref(v_D_156_);
v___x_162_ = lp_Tiling_StickPolyhex_ABSim_IndexTiling_xphase(v_D_156_, v_T_157_, v_c_158_, v_n_159_, v_j_160_);
v___x_163_ = lean_int_sub(v___x_161_, v___x_162_);
lean_dec(v___x_162_);
lean_dec(v___x_161_);
v___x_164_ = lp_Tiling_StickPolyhex_ABSim_IndexTiling_cphase(v_D_156_, v_T_157_, v_c_158_, v_n_159_, v_j_160_);
v___x_165_ = lean_int_add(v___x_163_, v___x_164_);
lean_dec(v___x_164_);
lean_dec(v___x_163_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_ABSim_IndexTiling_yphase___boxed(lean_object* v_D_166_, lean_object* v_T_167_, lean_object* v_c_168_, lean_object* v_n_169_, lean_object* v_j_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = lp_Tiling_StickPolyhex_ABSim_IndexTiling_yphase(v_D_166_, v_T_167_, v_c_168_, v_n_169_, v_j_170_);
lean_dec(v_j_170_);
return v_res_171_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_ABValues(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_ABIndex(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_Proofs_ABLineValues(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_ABValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_ABIndex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
