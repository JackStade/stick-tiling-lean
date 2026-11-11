// Lean compiler output
// Module: Tiling.Proofs.Schematic
// Imports: public import Init public meta import Init public import Tiling.Proofs.Weave
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Slot_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Slot_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Slot_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Slot_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Slot_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Slot_block_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Slot_block_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Slot_gapL_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Slot_gapL_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Slot_gapR_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Slot_gapR_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_Tiling_StickPolyhex_instDecidableEqSlot_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_instDecidableEqSlot_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_Tiling_StickPolyhex_instDecidableEqSlot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_instDecidableEqSlot___boxed(lean_object*, lean_object*);
static const lean_string_object lp_Tiling_StickPolyhex_instReprSlot_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "StickPolyhex.Slot.gapL"};
static const lean_object* lp_Tiling_StickPolyhex_instReprSlot_repr___closed__0 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprSlot_repr___closed__0_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_instReprSlot_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Tiling_StickPolyhex_instReprSlot_repr___closed__0_value)}};
static const lean_object* lp_Tiling_StickPolyhex_instReprSlot_repr___closed__1 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprSlot_repr___closed__1_value;
static const lean_string_object lp_Tiling_StickPolyhex_instReprSlot_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "StickPolyhex.Slot.gapR"};
static const lean_object* lp_Tiling_StickPolyhex_instReprSlot_repr___closed__2 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprSlot_repr___closed__2_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_instReprSlot_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Tiling_StickPolyhex_instReprSlot_repr___closed__2_value)}};
static const lean_object* lp_Tiling_StickPolyhex_instReprSlot_repr___closed__3 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprSlot_repr___closed__3_value;
static const lean_string_object lp_Tiling_StickPolyhex_instReprSlot_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "StickPolyhex.Slot.block"};
static const lean_object* lp_Tiling_StickPolyhex_instReprSlot_repr___closed__4 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprSlot_repr___closed__4_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_instReprSlot_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Tiling_StickPolyhex_instReprSlot_repr___closed__4_value)}};
static const lean_object* lp_Tiling_StickPolyhex_instReprSlot_repr___closed__5 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprSlot_repr___closed__5_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_instReprSlot_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_Tiling_StickPolyhex_instReprSlot_repr___closed__5_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_Tiling_StickPolyhex_instReprSlot_repr___closed__6 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprSlot_repr___closed__6_value;
static lean_once_cell_t lp_Tiling_StickPolyhex_instReprSlot_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_instReprSlot_repr___closed__7;
static lean_once_cell_t lp_Tiling_StickPolyhex_instReprSlot_repr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_instReprSlot_repr___closed__8;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_instReprSlot_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_instReprSlot_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_Tiling_StickPolyhex_instReprSlot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Tiling_StickPolyhex_instReprSlot_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Tiling_StickPolyhex_instReprSlot___closed__0 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprSlot___closed__0_value;
LEAN_EXPORT const lean_object* lp_Tiling_StickPolyhex_instReprSlot = (const lean_object*)&lp_Tiling_StickPolyhex_instReprSlot___closed__0_value;
LEAN_EXPORT uint8_t lp_Tiling_StickPolyhex_Slot_instDecidableIsGap(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Slot_instDecidableIsGap___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling___private_Tiling_Proofs_Schematic_0__StickPolyhex_instDecidableEqSlot_decEq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling___private_Tiling_Proofs_Schematic_0__StickPolyhex_instDecidableEqSlot_decEq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Slot_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Slot_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_Tiling_StickPolyhex_Slot_ctorIdx(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Slot_ctorElim___redArg(lean_object* v_t_7_, lean_object* v_k_8_){
_start:
{
if (lean_obj_tag(v_t_7_) == 0)
{
lean_object* v_j_9_; lean_object* v___x_10_; 
v_j_9_ = lean_ctor_get(v_t_7_, 0);
lean_inc(v_j_9_);
lean_dec_ref_known(v_t_7_, 1);
v___x_10_ = lean_apply_1(v_k_8_, v_j_9_);
return v___x_10_;
}
else
{
lean_dec(v_t_7_);
return v_k_8_;
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Slot_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, lean_object* v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lp_Tiling_StickPolyhex_Slot_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Slot_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_Tiling_StickPolyhex_Slot_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Slot_block_elim___redArg(lean_object* v_t_23_, lean_object* v_block_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_Tiling_StickPolyhex_Slot_ctorElim___redArg(v_t_23_, v_block_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Slot_block_elim(lean_object* v_motive_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_block_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lp_Tiling_StickPolyhex_Slot_ctorElim___redArg(v_t_27_, v_block_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Slot_gapL_elim___redArg(lean_object* v_t_31_, lean_object* v_gapL_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lp_Tiling_StickPolyhex_Slot_ctorElim___redArg(v_t_31_, v_gapL_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Slot_gapL_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_gapL_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lp_Tiling_StickPolyhex_Slot_ctorElim___redArg(v_t_35_, v_gapL_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Slot_gapR_elim___redArg(lean_object* v_t_39_, lean_object* v_gapR_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lp_Tiling_StickPolyhex_Slot_ctorElim___redArg(v_t_39_, v_gapR_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Slot_gapR_elim(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_gapR_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lp_Tiling_StickPolyhex_Slot_ctorElim___redArg(v_t_43_, v_gapR_45_);
return v___x_46_;
}
}
LEAN_EXPORT uint8_t lp_Tiling_StickPolyhex_instDecidableEqSlot_decEq(lean_object* v_x_47_, lean_object* v_x_48_){
_start:
{
switch(lean_obj_tag(v_x_47_))
{
case 0:
{
lean_object* v_j_49_; uint8_t v___x_50_; 
v_j_49_ = lean_ctor_get(v_x_47_, 0);
v___x_50_ = 0;
if (lean_obj_tag(v_x_48_) == 0)
{
lean_object* v_j_51_; uint8_t v___x_52_; 
v_j_51_ = lean_ctor_get(v_x_48_, 0);
v___x_52_ = lean_nat_dec_eq(v_j_49_, v_j_51_);
if (v___x_52_ == 0)
{
return v___x_50_;
}
else
{
return v___x_52_;
}
}
else
{
return v___x_50_;
}
}
case 1:
{
if (lean_obj_tag(v_x_48_) == 1)
{
uint8_t v___x_53_; 
v___x_53_ = 1;
return v___x_53_;
}
else
{
uint8_t v___x_54_; 
v___x_54_ = 0;
return v___x_54_;
}
}
default: 
{
if (lean_obj_tag(v_x_48_) == 2)
{
uint8_t v___x_55_; 
v___x_55_ = 1;
return v___x_55_;
}
else
{
uint8_t v___x_56_; 
v___x_56_ = 0;
return v___x_56_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_instDecidableEqSlot_decEq___boxed(lean_object* v_x_57_, lean_object* v_x_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = lp_Tiling_StickPolyhex_instDecidableEqSlot_decEq(v_x_57_, v_x_58_);
lean_dec(v_x_58_);
lean_dec(v_x_57_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT uint8_t lp_Tiling_StickPolyhex_instDecidableEqSlot(lean_object* v_x_61_, lean_object* v_x_62_){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = lp_Tiling_StickPolyhex_instDecidableEqSlot_decEq(v_x_61_, v_x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_instDecidableEqSlot___boxed(lean_object* v_x_64_, lean_object* v_x_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = lp_Tiling_StickPolyhex_instDecidableEqSlot(v_x_64_, v_x_65_);
lean_dec(v_x_65_);
lean_dec(v_x_64_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_instReprSlot_repr___closed__7(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_unsigned_to_nat(2u);
v___x_81_ = lean_nat_to_int(v___x_80_);
return v___x_81_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_instReprSlot_repr___closed__8(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = lean_unsigned_to_nat(1u);
v___x_83_ = lean_nat_to_int(v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_instReprSlot_repr(lean_object* v_x_84_, lean_object* v_prec_85_){
_start:
{
lean_object* v___y_87_; lean_object* v___y_94_; 
switch(lean_obj_tag(v_x_84_))
{
case 0:
{
lean_object* v_j_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_120_; 
v_j_100_ = lean_ctor_get(v_x_84_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v_x_84_);
if (v_isSharedCheck_120_ == 0)
{
v___x_102_ = v_x_84_;
v_isShared_103_ = v_isSharedCheck_120_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_j_100_);
lean_dec(v_x_84_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_120_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___y_105_; lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = lean_unsigned_to_nat(1024u);
v___x_117_ = lean_nat_dec_le(v___x_116_, v_prec_85_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; 
v___x_118_ = lean_obj_once(&lp_Tiling_StickPolyhex_instReprSlot_repr___closed__7, &lp_Tiling_StickPolyhex_instReprSlot_repr___closed__7_once, _init_lp_Tiling_StickPolyhex_instReprSlot_repr___closed__7);
v___y_105_ = v___x_118_;
goto v___jp_104_;
}
else
{
lean_object* v___x_119_; 
v___x_119_ = lean_obj_once(&lp_Tiling_StickPolyhex_instReprSlot_repr___closed__8, &lp_Tiling_StickPolyhex_instReprSlot_repr___closed__8_once, _init_lp_Tiling_StickPolyhex_instReprSlot_repr___closed__8);
v___y_105_ = v___x_119_;
goto v___jp_104_;
}
v___jp_104_:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_106_ = ((lean_object*)(lp_Tiling_StickPolyhex_instReprSlot_repr___closed__6));
v___x_107_ = l_Nat_reprFast(v_j_100_);
if (v_isShared_103_ == 0)
{
lean_ctor_set_tag(v___x_102_, 3);
lean_ctor_set(v___x_102_, 0, v___x_107_);
v___x_109_ = v___x_102_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_107_);
v___x_109_ = v_reuseFailAlloc_115_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_106_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
lean_inc(v___y_105_);
v___x_111_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_111_, 0, v___y_105_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
v___x_112_ = 0;
v___x_113_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_113_, 0, v___x_111_);
lean_ctor_set_uint8(v___x_113_, sizeof(void*)*1, v___x_112_);
v___x_114_ = l_Repr_addAppParen(v___x_113_, v_prec_85_);
return v___x_114_;
}
}
}
}
case 1:
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = lean_unsigned_to_nat(1024u);
v___x_122_ = lean_nat_dec_le(v___x_121_, v_prec_85_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; 
v___x_123_ = lean_obj_once(&lp_Tiling_StickPolyhex_instReprSlot_repr___closed__7, &lp_Tiling_StickPolyhex_instReprSlot_repr___closed__7_once, _init_lp_Tiling_StickPolyhex_instReprSlot_repr___closed__7);
v___y_87_ = v___x_123_;
goto v___jp_86_;
}
else
{
lean_object* v___x_124_; 
v___x_124_ = lean_obj_once(&lp_Tiling_StickPolyhex_instReprSlot_repr___closed__8, &lp_Tiling_StickPolyhex_instReprSlot_repr___closed__8_once, _init_lp_Tiling_StickPolyhex_instReprSlot_repr___closed__8);
v___y_87_ = v___x_124_;
goto v___jp_86_;
}
}
default: 
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = lean_unsigned_to_nat(1024u);
v___x_126_ = lean_nat_dec_le(v___x_125_, v_prec_85_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; 
v___x_127_ = lean_obj_once(&lp_Tiling_StickPolyhex_instReprSlot_repr___closed__7, &lp_Tiling_StickPolyhex_instReprSlot_repr___closed__7_once, _init_lp_Tiling_StickPolyhex_instReprSlot_repr___closed__7);
v___y_94_ = v___x_127_;
goto v___jp_93_;
}
else
{
lean_object* v___x_128_; 
v___x_128_ = lean_obj_once(&lp_Tiling_StickPolyhex_instReprSlot_repr___closed__8, &lp_Tiling_StickPolyhex_instReprSlot_repr___closed__8_once, _init_lp_Tiling_StickPolyhex_instReprSlot_repr___closed__8);
v___y_94_ = v___x_128_;
goto v___jp_93_;
}
}
}
v___jp_86_:
{
lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_88_ = ((lean_object*)(lp_Tiling_StickPolyhex_instReprSlot_repr___closed__1));
lean_inc(v___y_87_);
v___x_89_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_89_, 0, v___y_87_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = 0;
v___x_91_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set_uint8(v___x_91_, sizeof(void*)*1, v___x_90_);
v___x_92_ = l_Repr_addAppParen(v___x_91_, v_prec_85_);
return v___x_92_;
}
v___jp_93_:
{
lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_95_ = ((lean_object*)(lp_Tiling_StickPolyhex_instReprSlot_repr___closed__3));
lean_inc(v___y_94_);
v___x_96_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_96_, 0, v___y_94_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = 0;
v___x_98_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_98_, 0, v___x_96_);
lean_ctor_set_uint8(v___x_98_, sizeof(void*)*1, v___x_97_);
v___x_99_ = l_Repr_addAppParen(v___x_98_, v_prec_85_);
return v___x_99_;
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_instReprSlot_repr___boxed(lean_object* v_x_129_, lean_object* v_prec_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = lp_Tiling_StickPolyhex_instReprSlot_repr(v_x_129_, v_prec_130_);
lean_dec(v_prec_130_);
return v_res_131_;
}
}
LEAN_EXPORT uint8_t lp_Tiling_StickPolyhex_Slot_instDecidableIsGap(lean_object* v_s_134_){
_start:
{
if (lean_obj_tag(v_s_134_) == 0)
{
uint8_t v___x_135_; 
v___x_135_ = 0;
return v___x_135_;
}
else
{
uint8_t v___x_136_; 
v___x_136_ = 1;
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Slot_instDecidableIsGap___boxed(lean_object* v_s_137_){
_start:
{
uint8_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = lp_Tiling_StickPolyhex_Slot_instDecidableIsGap(v_s_137_);
lean_dec(v_s_137_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT lean_object* lp_Tiling___private_Tiling_Proofs_Schematic_0__StickPolyhex_instDecidableEqSlot_decEq_match__1_splitter___redArg(lean_object* v_x_140_, lean_object* v_x_141_, lean_object* v_h__1_142_, lean_object* v_h__2_143_, lean_object* v_h__3_144_, lean_object* v_h__4_145_, lean_object* v_h__5_146_, lean_object* v_h__6_147_, lean_object* v_h__7_148_, lean_object* v_h__8_149_, lean_object* v_h__9_150_){
_start:
{
switch(lean_obj_tag(v_x_140_))
{
case 0:
{
lean_dec(v_h__9_150_);
lean_dec(v_h__8_149_);
lean_dec(v_h__7_148_);
lean_dec(v_h__6_147_);
lean_dec(v_h__5_146_);
lean_dec(v_h__4_145_);
switch(lean_obj_tag(v_x_141_))
{
case 0:
{
lean_object* v_j_151_; lean_object* v_j_152_; lean_object* v___x_153_; 
lean_dec(v_h__3_144_);
lean_dec(v_h__2_143_);
v_j_151_ = lean_ctor_get(v_x_140_, 0);
lean_inc(v_j_151_);
lean_dec_ref_known(v_x_140_, 1);
v_j_152_ = lean_ctor_get(v_x_141_, 0);
lean_inc(v_j_152_);
lean_dec_ref_known(v_x_141_, 1);
v___x_153_ = lean_apply_2(v_h__1_142_, v_j_151_, v_j_152_);
return v___x_153_;
}
case 1:
{
lean_object* v_j_154_; lean_object* v___x_155_; 
lean_dec(v_h__3_144_);
lean_dec(v_h__1_142_);
v_j_154_ = lean_ctor_get(v_x_140_, 0);
lean_inc(v_j_154_);
lean_dec_ref_known(v_x_140_, 1);
v___x_155_ = lean_apply_1(v_h__2_143_, v_j_154_);
return v___x_155_;
}
default: 
{
lean_object* v_j_156_; lean_object* v___x_157_; 
lean_dec(v_h__2_143_);
lean_dec(v_h__1_142_);
v_j_156_ = lean_ctor_get(v_x_140_, 0);
lean_inc(v_j_156_);
lean_dec_ref_known(v_x_140_, 1);
v___x_157_ = lean_apply_1(v_h__3_144_, v_j_156_);
return v___x_157_;
}
}
}
case 1:
{
lean_dec(v_h__9_150_);
lean_dec(v_h__8_149_);
lean_dec(v_h__7_148_);
lean_dec(v_h__3_144_);
lean_dec(v_h__2_143_);
lean_dec(v_h__1_142_);
switch(lean_obj_tag(v_x_141_))
{
case 0:
{
lean_object* v_j_158_; lean_object* v___x_159_; 
lean_dec(v_h__6_147_);
lean_dec(v_h__5_146_);
v_j_158_ = lean_ctor_get(v_x_141_, 0);
lean_inc(v_j_158_);
lean_dec_ref_known(v_x_141_, 1);
v___x_159_ = lean_apply_1(v_h__4_145_, v_j_158_);
return v___x_159_;
}
case 1:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_dec(v_h__6_147_);
lean_dec(v_h__4_145_);
v___x_160_ = lean_box(0);
v___x_161_ = lean_apply_1(v_h__5_146_, v___x_160_);
return v___x_161_;
}
default: 
{
lean_object* v___x_162_; lean_object* v___x_163_; 
lean_dec(v_h__5_146_);
lean_dec(v_h__4_145_);
v___x_162_ = lean_box(0);
v___x_163_ = lean_apply_1(v_h__6_147_, v___x_162_);
return v___x_163_;
}
}
}
default: 
{
lean_dec(v_h__6_147_);
lean_dec(v_h__5_146_);
lean_dec(v_h__4_145_);
lean_dec(v_h__3_144_);
lean_dec(v_h__2_143_);
lean_dec(v_h__1_142_);
switch(lean_obj_tag(v_x_141_))
{
case 0:
{
lean_object* v_j_164_; lean_object* v___x_165_; 
lean_dec(v_h__9_150_);
lean_dec(v_h__8_149_);
v_j_164_ = lean_ctor_get(v_x_141_, 0);
lean_inc(v_j_164_);
lean_dec_ref_known(v_x_141_, 1);
v___x_165_ = lean_apply_1(v_h__7_148_, v_j_164_);
return v___x_165_;
}
case 1:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec(v_h__9_150_);
lean_dec(v_h__7_148_);
v___x_166_ = lean_box(0);
v___x_167_ = lean_apply_1(v_h__8_149_, v___x_166_);
return v___x_167_;
}
default: 
{
lean_object* v___x_168_; lean_object* v___x_169_; 
lean_dec(v_h__8_149_);
lean_dec(v_h__7_148_);
v___x_168_ = lean_box(0);
v___x_169_ = lean_apply_1(v_h__9_150_, v___x_168_);
return v___x_169_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Tiling___private_Tiling_Proofs_Schematic_0__StickPolyhex_instDecidableEqSlot_decEq_match__1_splitter(lean_object* v_motive_170_, lean_object* v_x_171_, lean_object* v_x_172_, lean_object* v_h__1_173_, lean_object* v_h__2_174_, lean_object* v_h__3_175_, lean_object* v_h__4_176_, lean_object* v_h__5_177_, lean_object* v_h__6_178_, lean_object* v_h__7_179_, lean_object* v_h__8_180_, lean_object* v_h__9_181_){
_start:
{
switch(lean_obj_tag(v_x_171_))
{
case 0:
{
lean_dec(v_h__9_181_);
lean_dec(v_h__8_180_);
lean_dec(v_h__7_179_);
lean_dec(v_h__6_178_);
lean_dec(v_h__5_177_);
lean_dec(v_h__4_176_);
switch(lean_obj_tag(v_x_172_))
{
case 0:
{
lean_object* v_j_182_; lean_object* v_j_183_; lean_object* v___x_184_; 
lean_dec(v_h__3_175_);
lean_dec(v_h__2_174_);
v_j_182_ = lean_ctor_get(v_x_171_, 0);
lean_inc(v_j_182_);
lean_dec_ref_known(v_x_171_, 1);
v_j_183_ = lean_ctor_get(v_x_172_, 0);
lean_inc(v_j_183_);
lean_dec_ref_known(v_x_172_, 1);
v___x_184_ = lean_apply_2(v_h__1_173_, v_j_182_, v_j_183_);
return v___x_184_;
}
case 1:
{
lean_object* v_j_185_; lean_object* v___x_186_; 
lean_dec(v_h__3_175_);
lean_dec(v_h__1_173_);
v_j_185_ = lean_ctor_get(v_x_171_, 0);
lean_inc(v_j_185_);
lean_dec_ref_known(v_x_171_, 1);
v___x_186_ = lean_apply_1(v_h__2_174_, v_j_185_);
return v___x_186_;
}
default: 
{
lean_object* v_j_187_; lean_object* v___x_188_; 
lean_dec(v_h__2_174_);
lean_dec(v_h__1_173_);
v_j_187_ = lean_ctor_get(v_x_171_, 0);
lean_inc(v_j_187_);
lean_dec_ref_known(v_x_171_, 1);
v___x_188_ = lean_apply_1(v_h__3_175_, v_j_187_);
return v___x_188_;
}
}
}
case 1:
{
lean_dec(v_h__9_181_);
lean_dec(v_h__8_180_);
lean_dec(v_h__7_179_);
lean_dec(v_h__3_175_);
lean_dec(v_h__2_174_);
lean_dec(v_h__1_173_);
switch(lean_obj_tag(v_x_172_))
{
case 0:
{
lean_object* v_j_189_; lean_object* v___x_190_; 
lean_dec(v_h__6_178_);
lean_dec(v_h__5_177_);
v_j_189_ = lean_ctor_get(v_x_172_, 0);
lean_inc(v_j_189_);
lean_dec_ref_known(v_x_172_, 1);
v___x_190_ = lean_apply_1(v_h__4_176_, v_j_189_);
return v___x_190_;
}
case 1:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
lean_dec(v_h__6_178_);
lean_dec(v_h__4_176_);
v___x_191_ = lean_box(0);
v___x_192_ = lean_apply_1(v_h__5_177_, v___x_191_);
return v___x_192_;
}
default: 
{
lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec(v_h__5_177_);
lean_dec(v_h__4_176_);
v___x_193_ = lean_box(0);
v___x_194_ = lean_apply_1(v_h__6_178_, v___x_193_);
return v___x_194_;
}
}
}
default: 
{
lean_dec(v_h__6_178_);
lean_dec(v_h__5_177_);
lean_dec(v_h__4_176_);
lean_dec(v_h__3_175_);
lean_dec(v_h__2_174_);
lean_dec(v_h__1_173_);
switch(lean_obj_tag(v_x_172_))
{
case 0:
{
lean_object* v_j_195_; lean_object* v___x_196_; 
lean_dec(v_h__9_181_);
lean_dec(v_h__8_180_);
v_j_195_ = lean_ctor_get(v_x_172_, 0);
lean_inc(v_j_195_);
lean_dec_ref_known(v_x_172_, 1);
v___x_196_ = lean_apply_1(v_h__7_179_, v_j_195_);
return v___x_196_;
}
case 1:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec(v_h__9_181_);
lean_dec(v_h__7_179_);
v___x_197_ = lean_box(0);
v___x_198_ = lean_apply_1(v_h__8_180_, v___x_197_);
return v___x_198_;
}
default: 
{
lean_object* v___x_199_; lean_object* v___x_200_; 
lean_dec(v_h__8_180_);
lean_dec(v_h__7_179_);
v___x_199_ = lean_box(0);
v___x_200_ = lean_apply_1(v_h__9_181_, v___x_199_);
return v___x_200_;
}
}
}
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_Weave(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_Proofs_Schematic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_Weave(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
