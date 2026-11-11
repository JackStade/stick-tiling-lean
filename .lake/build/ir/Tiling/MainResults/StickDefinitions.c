// Lean compiler output
// Module: Tiling.MainResults.StickDefinitions
// Imports: public import Init public meta import Init public import Tiling.MainResults.HexGrid
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
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Fin_cases___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_commRing(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
extern lean_object* lp_Tiling_StickPolyhex_HexDir_W;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_x1_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_x1_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_x2_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_x2_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_y1_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_y1_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_y2_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_y2_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_z1_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_z1_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_z2_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_z2_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_a_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_a_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_b_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_b_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_c_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_c_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_d_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_d_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_Tiling_StickPolyhex_instDecidableEqStickEdge_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_instDecidableEqStickEdge_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_Tiling_StickPolyhex_instDecidableEqStickEdge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_instDecidableEqStickEdge___boxed(lean_object*, lean_object*);
static const lean_string_object lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "StickPolyhex.StickEdge.x1"};
static const lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__0 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__0_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__0_value)}};
static const lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__1 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__1_value;
static const lean_string_object lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "StickPolyhex.StickEdge.x2"};
static const lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__2 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__2_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__2_value)}};
static const lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__3 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__3_value;
static const lean_string_object lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "StickPolyhex.StickEdge.y1"};
static const lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__4 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__4_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__4_value)}};
static const lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__5 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__5_value;
static const lean_string_object lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "StickPolyhex.StickEdge.y2"};
static const lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__6 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__6_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__6_value)}};
static const lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__7 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__7_value;
static const lean_string_object lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "StickPolyhex.StickEdge.z1"};
static const lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__8 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__8_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__8_value)}};
static const lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__9 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__9_value;
static const lean_string_object lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "StickPolyhex.StickEdge.z2"};
static const lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__10 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__10_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__10_value)}};
static const lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__11 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__11_value;
static lean_once_cell_t lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12;
static lean_once_cell_t lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13;
static const lean_string_object lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "StickPolyhex.StickEdge.a"};
static const lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__14 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__14_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__14_value)}};
static const lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__15 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__15_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__15_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__16 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__16_value;
static const lean_string_object lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "StickPolyhex.StickEdge.b"};
static const lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__17 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__17_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__17_value)}};
static const lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__18 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__18_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__18_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__19 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__19_value;
static const lean_string_object lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "StickPolyhex.StickEdge.c"};
static const lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__20 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__20_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__20_value)}};
static const lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__21 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__21_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__21_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__22 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__22_value;
static const lean_string_object lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "StickPolyhex.StickEdge.d"};
static const lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__23 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__23_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__23_value)}};
static const lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__24 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__24_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__24_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__25 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__25_value;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_Tiling_StickPolyhex_instReprStickEdge___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Tiling_StickPolyhex_instReprStickEdge_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Tiling_StickPolyhex_instReprStickEdge___closed__0 = (const lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge___closed__0_value;
LEAN_EXPORT const lean_object* lp_Tiling_StickPolyhex_instReprStickEdge = (const lean_object*)&lp_Tiling_StickPolyhex_instReprStickEdge___closed__0_value;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_frameLabel___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_frameLabel___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_frameLabel___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_frameLabel___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_Tiling_StickPolyhex_frameLabel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Tiling_StickPolyhex_frameLabel___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Tiling_StickPolyhex_frameLabel___closed__0 = (const lean_object*)&lp_Tiling_StickPolyhex_frameLabel___closed__0_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_frameLabel___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_Tiling_StickPolyhex_frameLabel___closed__1 = (const lean_object*)&lp_Tiling_StickPolyhex_frameLabel___closed__1_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_frameLabel___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* lp_Tiling_StickPolyhex_frameLabel___closed__2 = (const lean_object*)&lp_Tiling_StickPolyhex_frameLabel___closed__2_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_frameLabel___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* lp_Tiling_StickPolyhex_frameLabel___closed__3 = (const lean_object*)&lp_Tiling_StickPolyhex_frameLabel___closed__3_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_frameLabel___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_Tiling_StickPolyhex_frameLabel___closed__4 = (const lean_object*)&lp_Tiling_StickPolyhex_frameLabel___closed__4_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_frameLabel___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* lp_Tiling_StickPolyhex_frameLabel___closed__5 = (const lean_object*)&lp_Tiling_StickPolyhex_frameLabel___closed__5_value;
static const lean_ctor_object lp_Tiling_StickPolyhex_frameLabel___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* lp_Tiling_StickPolyhex_frameLabel___closed__6 = (const lean_object*)&lp_Tiling_StickPolyhex_frameLabel___closed__6_value;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_frameLabel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_frameLabel___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_Tiling_StickPolyhex_StickTiling_labelOf___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_StickTiling_labelOf___redArg___closed__0;
static lean_once_cell_t lp_Tiling_StickPolyhex_StickTiling_labelOf___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_StickTiling_labelOf___redArg___closed__1;
static lean_once_cell_t lp_Tiling_StickPolyhex_StickTiling_labelOf___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_StickTiling_labelOf___redArg___closed__2;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_labelOf___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_labelOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_labelOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_markedRules___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_markedRules___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_markedRules(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_markedRules___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_ctorIdx(lean_object* v_x_1_){
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
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
case 4:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
case 5:
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
case 6:
{
lean_object* v___x_8_; 
v___x_8_ = lean_unsigned_to_nat(6u);
return v___x_8_;
}
case 7:
{
lean_object* v___x_9_; 
v___x_9_ = lean_unsigned_to_nat(7u);
return v___x_9_;
}
case 8:
{
lean_object* v___x_10_; 
v___x_10_ = lean_unsigned_to_nat(8u);
return v___x_10_;
}
default: 
{
lean_object* v___x_11_; 
v___x_11_ = lean_unsigned_to_nat(9u);
return v___x_11_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_ctorIdx___boxed(lean_object* v_x_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_Tiling_StickPolyhex_StickEdge_ctorIdx(v_x_12_);
lean_dec(v_x_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_ctorElim___redArg(lean_object* v_t_14_, lean_object* v_k_15_){
_start:
{
switch(lean_obj_tag(v_t_14_))
{
case 6:
{
lean_object* v_a_16_; lean_object* v___x_17_; 
v_a_16_ = lean_ctor_get(v_t_14_, 0);
lean_inc(v_a_16_);
lean_dec_ref_known(v_t_14_, 1);
v___x_17_ = lean_apply_1(v_k_15_, v_a_16_);
return v___x_17_;
}
case 7:
{
lean_object* v_a_18_; lean_object* v___x_19_; 
v_a_18_ = lean_ctor_get(v_t_14_, 0);
lean_inc(v_a_18_);
lean_dec_ref_known(v_t_14_, 1);
v___x_19_ = lean_apply_1(v_k_15_, v_a_18_);
return v___x_19_;
}
case 8:
{
lean_object* v_a_20_; lean_object* v___x_21_; 
v_a_20_ = lean_ctor_get(v_t_14_, 0);
lean_inc(v_a_20_);
lean_dec_ref_known(v_t_14_, 1);
v___x_21_ = lean_apply_1(v_k_15_, v_a_20_);
return v___x_21_;
}
case 9:
{
lean_object* v_a_22_; lean_object* v___x_23_; 
v_a_22_ = lean_ctor_get(v_t_14_, 0);
lean_inc(v_a_22_);
lean_dec_ref_known(v_t_14_, 1);
v___x_23_ = lean_apply_1(v_k_15_, v_a_22_);
return v___x_23_;
}
default: 
{
lean_dec(v_t_14_);
return v_k_15_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_ctorElim(lean_object* v_motive_24_, lean_object* v_ctorIdx_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_k_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lp_Tiling_StickPolyhex_StickEdge_ctorElim___redArg(v_t_26_, v_k_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_ctorElim___boxed(lean_object* v_motive_30_, lean_object* v_ctorIdx_31_, lean_object* v_t_32_, lean_object* v_h_33_, lean_object* v_k_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = lp_Tiling_StickPolyhex_StickEdge_ctorElim(v_motive_30_, v_ctorIdx_31_, v_t_32_, v_h_33_, v_k_34_);
lean_dec(v_ctorIdx_31_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_x1_elim___redArg(lean_object* v_t_36_, lean_object* v_x1_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lp_Tiling_StickPolyhex_StickEdge_ctorElim___redArg(v_t_36_, v_x1_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_x1_elim(lean_object* v_motive_39_, lean_object* v_t_40_, lean_object* v_h_41_, lean_object* v_x1_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lp_Tiling_StickPolyhex_StickEdge_ctorElim___redArg(v_t_40_, v_x1_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_x2_elim___redArg(lean_object* v_t_44_, lean_object* v_x2_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lp_Tiling_StickPolyhex_StickEdge_ctorElim___redArg(v_t_44_, v_x2_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_x2_elim(lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_x2_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lp_Tiling_StickPolyhex_StickEdge_ctorElim___redArg(v_t_48_, v_x2_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_y1_elim___redArg(lean_object* v_t_52_, lean_object* v_y1_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lp_Tiling_StickPolyhex_StickEdge_ctorElim___redArg(v_t_52_, v_y1_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_y1_elim(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_y1_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lp_Tiling_StickPolyhex_StickEdge_ctorElim___redArg(v_t_56_, v_y1_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_y2_elim___redArg(lean_object* v_t_60_, lean_object* v_y2_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lp_Tiling_StickPolyhex_StickEdge_ctorElim___redArg(v_t_60_, v_y2_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_y2_elim(lean_object* v_motive_63_, lean_object* v_t_64_, lean_object* v_h_65_, lean_object* v_y2_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lp_Tiling_StickPolyhex_StickEdge_ctorElim___redArg(v_t_64_, v_y2_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_z1_elim___redArg(lean_object* v_t_68_, lean_object* v_z1_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lp_Tiling_StickPolyhex_StickEdge_ctorElim___redArg(v_t_68_, v_z1_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_z1_elim(lean_object* v_motive_71_, lean_object* v_t_72_, lean_object* v_h_73_, lean_object* v_z1_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lp_Tiling_StickPolyhex_StickEdge_ctorElim___redArg(v_t_72_, v_z1_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_z2_elim___redArg(lean_object* v_t_76_, lean_object* v_z2_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lp_Tiling_StickPolyhex_StickEdge_ctorElim___redArg(v_t_76_, v_z2_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_z2_elim(lean_object* v_motive_79_, lean_object* v_t_80_, lean_object* v_h_81_, lean_object* v_z2_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = lp_Tiling_StickPolyhex_StickEdge_ctorElim___redArg(v_t_80_, v_z2_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_a_elim___redArg(lean_object* v_t_84_, lean_object* v_a_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lp_Tiling_StickPolyhex_StickEdge_ctorElim___redArg(v_t_84_, v_a_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_a_elim(lean_object* v_motive_87_, lean_object* v_t_88_, lean_object* v_h_89_, lean_object* v_a_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lp_Tiling_StickPolyhex_StickEdge_ctorElim___redArg(v_t_88_, v_a_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_b_elim___redArg(lean_object* v_t_92_, lean_object* v_b_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lp_Tiling_StickPolyhex_StickEdge_ctorElim___redArg(v_t_92_, v_b_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_b_elim(lean_object* v_motive_95_, lean_object* v_t_96_, lean_object* v_h_97_, lean_object* v_b_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lp_Tiling_StickPolyhex_StickEdge_ctorElim___redArg(v_t_96_, v_b_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_c_elim___redArg(lean_object* v_t_100_, lean_object* v_c_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lp_Tiling_StickPolyhex_StickEdge_ctorElim___redArg(v_t_100_, v_c_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_c_elim(lean_object* v_motive_103_, lean_object* v_t_104_, lean_object* v_h_105_, lean_object* v_c_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = lp_Tiling_StickPolyhex_StickEdge_ctorElim___redArg(v_t_104_, v_c_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_d_elim___redArg(lean_object* v_t_108_, lean_object* v_d_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lp_Tiling_StickPolyhex_StickEdge_ctorElim___redArg(v_t_108_, v_d_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickEdge_d_elim(lean_object* v_motive_111_, lean_object* v_t_112_, lean_object* v_h_113_, lean_object* v_d_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lp_Tiling_StickPolyhex_StickEdge_ctorElim___redArg(v_t_112_, v_d_114_);
return v___x_115_;
}
}
LEAN_EXPORT uint8_t lp_Tiling_StickPolyhex_instDecidableEqStickEdge_decEq(lean_object* v_x_116_, lean_object* v_x_117_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_118_ = lp_Tiling_StickPolyhex_StickEdge_ctorIdx(v_x_116_);
v___x_119_ = lp_Tiling_StickPolyhex_StickEdge_ctorIdx(v_x_117_);
v___x_120_ = lean_nat_dec_eq(v___x_118_, v___x_119_);
lean_dec(v___x_119_);
lean_dec(v___x_118_);
if (v___x_120_ == 0)
{
return v___x_120_;
}
else
{
switch(lean_obj_tag(v_x_116_))
{
case 6:
{
lean_object* v_a_121_; lean_object* v_a_122_; uint8_t v___x_123_; 
v_a_121_ = lean_ctor_get(v_x_116_, 0);
v_a_122_ = lean_ctor_get(v_x_117_, 0);
v___x_123_ = lean_nat_dec_eq(v_a_121_, v_a_122_);
return v___x_123_;
}
case 7:
{
lean_object* v_a_124_; lean_object* v_a_125_; uint8_t v___x_126_; 
v_a_124_ = lean_ctor_get(v_x_116_, 0);
v_a_125_ = lean_ctor_get(v_x_117_, 0);
v___x_126_ = lean_nat_dec_eq(v_a_124_, v_a_125_);
return v___x_126_;
}
case 8:
{
lean_object* v_a_127_; lean_object* v_a_128_; uint8_t v___x_129_; 
v_a_127_ = lean_ctor_get(v_x_116_, 0);
v_a_128_ = lean_ctor_get(v_x_117_, 0);
v___x_129_ = lean_nat_dec_eq(v_a_127_, v_a_128_);
return v___x_129_;
}
case 9:
{
lean_object* v_a_130_; lean_object* v_a_131_; uint8_t v___x_132_; 
v_a_130_ = lean_ctor_get(v_x_116_, 0);
v_a_131_ = lean_ctor_get(v_x_117_, 0);
v___x_132_ = lean_nat_dec_eq(v_a_130_, v_a_131_);
return v___x_132_;
}
default: 
{
return v___x_120_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_instDecidableEqStickEdge_decEq___boxed(lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = lp_Tiling_StickPolyhex_instDecidableEqStickEdge_decEq(v_x_133_, v_x_134_);
lean_dec(v_x_134_);
lean_dec(v_x_133_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT uint8_t lp_Tiling_StickPolyhex_instDecidableEqStickEdge(lean_object* v_x_137_, lean_object* v_x_138_){
_start:
{
uint8_t v___x_139_; 
v___x_139_ = lp_Tiling_StickPolyhex_instDecidableEqStickEdge_decEq(v_x_137_, v_x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_instDecidableEqStickEdge___boxed(lean_object* v_x_140_, lean_object* v_x_141_){
_start:
{
uint8_t v_res_142_; lean_object* v_r_143_; 
v_res_142_ = lp_Tiling_StickPolyhex_instDecidableEqStickEdge(v_x_140_, v_x_141_);
lean_dec(v_x_141_);
lean_dec(v_x_140_);
v_r_143_ = lean_box(v_res_142_);
return v_r_143_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_unsigned_to_nat(2u);
v___x_163_ = lean_nat_to_int(v___x_162_);
return v___x_163_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_unsigned_to_nat(1u);
v___x_165_ = lean_nat_to_int(v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr(lean_object* v_x_190_, lean_object* v_prec_191_){
_start:
{
lean_object* v___y_193_; lean_object* v___y_200_; lean_object* v___y_207_; lean_object* v___y_214_; lean_object* v___y_221_; lean_object* v___y_228_; 
switch(lean_obj_tag(v_x_190_))
{
case 0:
{
lean_object* v___x_234_; uint8_t v___x_235_; 
v___x_234_ = lean_unsigned_to_nat(1024u);
v___x_235_ = lean_nat_dec_le(v___x_234_, v_prec_191_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; 
v___x_236_ = lean_obj_once(&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12, &lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12_once, _init_lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12);
v___y_193_ = v___x_236_;
goto v___jp_192_;
}
else
{
lean_object* v___x_237_; 
v___x_237_ = lean_obj_once(&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13, &lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13_once, _init_lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13);
v___y_193_ = v___x_237_;
goto v___jp_192_;
}
}
case 1:
{
lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_238_ = lean_unsigned_to_nat(1024u);
v___x_239_ = lean_nat_dec_le(v___x_238_, v_prec_191_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; 
v___x_240_ = lean_obj_once(&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12, &lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12_once, _init_lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12);
v___y_200_ = v___x_240_;
goto v___jp_199_;
}
else
{
lean_object* v___x_241_; 
v___x_241_ = lean_obj_once(&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13, &lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13_once, _init_lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13);
v___y_200_ = v___x_241_;
goto v___jp_199_;
}
}
case 2:
{
lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_242_ = lean_unsigned_to_nat(1024u);
v___x_243_ = lean_nat_dec_le(v___x_242_, v_prec_191_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; 
v___x_244_ = lean_obj_once(&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12, &lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12_once, _init_lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12);
v___y_207_ = v___x_244_;
goto v___jp_206_;
}
else
{
lean_object* v___x_245_; 
v___x_245_ = lean_obj_once(&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13, &lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13_once, _init_lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13);
v___y_207_ = v___x_245_;
goto v___jp_206_;
}
}
case 3:
{
lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_246_ = lean_unsigned_to_nat(1024u);
v___x_247_ = lean_nat_dec_le(v___x_246_, v_prec_191_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; 
v___x_248_ = lean_obj_once(&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12, &lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12_once, _init_lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12);
v___y_214_ = v___x_248_;
goto v___jp_213_;
}
else
{
lean_object* v___x_249_; 
v___x_249_ = lean_obj_once(&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13, &lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13_once, _init_lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13);
v___y_214_ = v___x_249_;
goto v___jp_213_;
}
}
case 4:
{
lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_250_ = lean_unsigned_to_nat(1024u);
v___x_251_ = lean_nat_dec_le(v___x_250_, v_prec_191_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; 
v___x_252_ = lean_obj_once(&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12, &lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12_once, _init_lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12);
v___y_221_ = v___x_252_;
goto v___jp_220_;
}
else
{
lean_object* v___x_253_; 
v___x_253_ = lean_obj_once(&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13, &lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13_once, _init_lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13);
v___y_221_ = v___x_253_;
goto v___jp_220_;
}
}
case 5:
{
lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_254_ = lean_unsigned_to_nat(1024u);
v___x_255_ = lean_nat_dec_le(v___x_254_, v_prec_191_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; 
v___x_256_ = lean_obj_once(&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12, &lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12_once, _init_lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12);
v___y_228_ = v___x_256_;
goto v___jp_227_;
}
else
{
lean_object* v___x_257_; 
v___x_257_ = lean_obj_once(&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13, &lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13_once, _init_lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13);
v___y_228_ = v___x_257_;
goto v___jp_227_;
}
}
case 6:
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_278_; 
v_a_258_ = lean_ctor_get(v_x_190_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v_x_190_);
if (v_isSharedCheck_278_ == 0)
{
v___x_260_ = v_x_190_;
v_isShared_261_ = v_isSharedCheck_278_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v_x_190_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_278_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___y_263_; lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_274_ = lean_unsigned_to_nat(1024u);
v___x_275_ = lean_nat_dec_le(v___x_274_, v_prec_191_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; 
v___x_276_ = lean_obj_once(&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12, &lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12_once, _init_lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12);
v___y_263_ = v___x_276_;
goto v___jp_262_;
}
else
{
lean_object* v___x_277_; 
v___x_277_ = lean_obj_once(&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13, &lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13_once, _init_lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13);
v___y_263_ = v___x_277_;
goto v___jp_262_;
}
v___jp_262_:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_264_ = ((lean_object*)(lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__16));
v___x_265_ = l_Nat_reprFast(v_a_258_);
if (v_isShared_261_ == 0)
{
lean_ctor_set_tag(v___x_260_, 3);
lean_ctor_set(v___x_260_, 0, v___x_265_);
v___x_267_ = v___x_260_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_265_);
v___x_267_ = v_reuseFailAlloc_273_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_268_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_264_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
lean_inc(v___y_263_);
v___x_269_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_269_, 0, v___y_263_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = 0;
v___x_271_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_271_, 0, v___x_269_);
lean_ctor_set_uint8(v___x_271_, sizeof(void*)*1, v___x_270_);
v___x_272_ = l_Repr_addAppParen(v___x_271_, v_prec_191_);
return v___x_272_;
}
}
}
}
case 7:
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_299_; 
v_a_279_ = lean_ctor_get(v_x_190_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v_x_190_);
if (v_isSharedCheck_299_ == 0)
{
v___x_281_ = v_x_190_;
v_isShared_282_ = v_isSharedCheck_299_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v_x_190_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_299_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___y_284_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = lean_unsigned_to_nat(1024u);
v___x_296_ = lean_nat_dec_le(v___x_295_, v_prec_191_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; 
v___x_297_ = lean_obj_once(&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12, &lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12_once, _init_lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12);
v___y_284_ = v___x_297_;
goto v___jp_283_;
}
else
{
lean_object* v___x_298_; 
v___x_298_ = lean_obj_once(&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13, &lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13_once, _init_lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13);
v___y_284_ = v___x_298_;
goto v___jp_283_;
}
v___jp_283_:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_285_ = ((lean_object*)(lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__19));
v___x_286_ = l_Nat_reprFast(v_a_279_);
if (v_isShared_282_ == 0)
{
lean_ctor_set_tag(v___x_281_, 3);
lean_ctor_set(v___x_281_, 0, v___x_286_);
v___x_288_ = v___x_281_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_286_);
v___x_288_ = v_reuseFailAlloc_294_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_289_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_285_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
lean_inc(v___y_284_);
v___x_290_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_290_, 0, v___y_284_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = 0;
v___x_292_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_292_, 0, v___x_290_);
lean_ctor_set_uint8(v___x_292_, sizeof(void*)*1, v___x_291_);
v___x_293_ = l_Repr_addAppParen(v___x_292_, v_prec_191_);
return v___x_293_;
}
}
}
}
case 8:
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_320_; 
v_a_300_ = lean_ctor_get(v_x_190_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v_x_190_);
if (v_isSharedCheck_320_ == 0)
{
v___x_302_ = v_x_190_;
v_isShared_303_ = v_isSharedCheck_320_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v_x_190_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_320_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___y_305_; lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_316_ = lean_unsigned_to_nat(1024u);
v___x_317_ = lean_nat_dec_le(v___x_316_, v_prec_191_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; 
v___x_318_ = lean_obj_once(&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12, &lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12_once, _init_lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12);
v___y_305_ = v___x_318_;
goto v___jp_304_;
}
else
{
lean_object* v___x_319_; 
v___x_319_ = lean_obj_once(&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13, &lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13_once, _init_lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13);
v___y_305_ = v___x_319_;
goto v___jp_304_;
}
v___jp_304_:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_309_; 
v___x_306_ = ((lean_object*)(lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__22));
v___x_307_ = l_Nat_reprFast(v_a_300_);
if (v_isShared_303_ == 0)
{
lean_ctor_set_tag(v___x_302_, 3);
lean_ctor_set(v___x_302_, 0, v___x_307_);
v___x_309_ = v___x_302_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_307_);
v___x_309_ = v_reuseFailAlloc_315_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_310_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_306_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
lean_inc(v___y_305_);
v___x_311_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_311_, 0, v___y_305_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
v___x_312_ = 0;
v___x_313_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_313_, 0, v___x_311_);
lean_ctor_set_uint8(v___x_313_, sizeof(void*)*1, v___x_312_);
v___x_314_ = l_Repr_addAppParen(v___x_313_, v_prec_191_);
return v___x_314_;
}
}
}
}
default: 
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_341_; 
v_a_321_ = lean_ctor_get(v_x_190_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v_x_190_);
if (v_isSharedCheck_341_ == 0)
{
v___x_323_ = v_x_190_;
v_isShared_324_ = v_isSharedCheck_341_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v_x_190_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_341_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___y_326_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_337_ = lean_unsigned_to_nat(1024u);
v___x_338_ = lean_nat_dec_le(v___x_337_, v_prec_191_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; 
v___x_339_ = lean_obj_once(&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12, &lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12_once, _init_lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__12);
v___y_326_ = v___x_339_;
goto v___jp_325_;
}
else
{
lean_object* v___x_340_; 
v___x_340_ = lean_obj_once(&lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13, &lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13_once, _init_lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__13);
v___y_326_ = v___x_340_;
goto v___jp_325_;
}
v___jp_325_:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_327_ = ((lean_object*)(lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__25));
v___x_328_ = l_Nat_reprFast(v_a_321_);
if (v_isShared_324_ == 0)
{
lean_ctor_set_tag(v___x_323_, 3);
lean_ctor_set(v___x_323_, 0, v___x_328_);
v___x_330_ = v___x_323_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_328_);
v___x_330_ = v_reuseFailAlloc_336_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_331_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_327_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
lean_inc(v___y_326_);
v___x_332_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_332_, 0, v___y_326_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = 0;
v___x_334_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_334_, 0, v___x_332_);
lean_ctor_set_uint8(v___x_334_, sizeof(void*)*1, v___x_333_);
v___x_335_ = l_Repr_addAppParen(v___x_334_, v_prec_191_);
return v___x_335_;
}
}
}
}
}
v___jp_192_:
{
lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_194_ = ((lean_object*)(lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__1));
lean_inc(v___y_193_);
v___x_195_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_195_, 0, v___y_193_);
lean_ctor_set(v___x_195_, 1, v___x_194_);
v___x_196_ = 0;
v___x_197_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_197_, 0, v___x_195_);
lean_ctor_set_uint8(v___x_197_, sizeof(void*)*1, v___x_196_);
v___x_198_ = l_Repr_addAppParen(v___x_197_, v_prec_191_);
return v___x_198_;
}
v___jp_199_:
{
lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_201_ = ((lean_object*)(lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__3));
lean_inc(v___y_200_);
v___x_202_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_202_, 0, v___y_200_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
v___x_203_ = 0;
v___x_204_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_204_, 0, v___x_202_);
lean_ctor_set_uint8(v___x_204_, sizeof(void*)*1, v___x_203_);
v___x_205_ = l_Repr_addAppParen(v___x_204_, v_prec_191_);
return v___x_205_;
}
v___jp_206_:
{
lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_208_ = ((lean_object*)(lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__5));
lean_inc(v___y_207_);
v___x_209_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_209_, 0, v___y_207_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v___x_210_ = 0;
v___x_211_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_211_, 0, v___x_209_);
lean_ctor_set_uint8(v___x_211_, sizeof(void*)*1, v___x_210_);
v___x_212_ = l_Repr_addAppParen(v___x_211_, v_prec_191_);
return v___x_212_;
}
v___jp_213_:
{
lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_215_ = ((lean_object*)(lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__7));
lean_inc(v___y_214_);
v___x_216_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_216_, 0, v___y_214_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
v___x_217_ = 0;
v___x_218_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_218_, 0, v___x_216_);
lean_ctor_set_uint8(v___x_218_, sizeof(void*)*1, v___x_217_);
v___x_219_ = l_Repr_addAppParen(v___x_218_, v_prec_191_);
return v___x_219_;
}
v___jp_220_:
{
lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_222_ = ((lean_object*)(lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__9));
lean_inc(v___y_221_);
v___x_223_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_223_, 0, v___y_221_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = 0;
v___x_225_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_225_, 0, v___x_223_);
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*1, v___x_224_);
v___x_226_ = l_Repr_addAppParen(v___x_225_, v_prec_191_);
return v___x_226_;
}
v___jp_227_:
{
lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_229_ = ((lean_object*)(lp_Tiling_StickPolyhex_instReprStickEdge_repr___closed__11));
lean_inc(v___y_228_);
v___x_230_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_230_, 0, v___y_228_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = 0;
v___x_232_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_232_, 0, v___x_230_);
lean_ctor_set_uint8(v___x_232_, sizeof(void*)*1, v___x_231_);
v___x_233_ = l_Repr_addAppParen(v___x_232_, v_prec_191_);
return v___x_233_;
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_instReprStickEdge_repr___boxed(lean_object* v_x_342_, lean_object* v_prec_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = lp_Tiling_StickPolyhex_instReprStickEdge_repr(v_x_342_, v_prec_343_);
lean_dec(v_prec_343_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_frameLabel___lam__0(lean_object* v___y_347_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_frameLabel___lam__0___boxed(lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = lp_Tiling_StickPolyhex_frameLabel___lam__0(v___y_348_);
lean_dec(v___y_348_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_frameLabel___lam__1(lean_object* v___y_350_, lean_object* v___f_351_, lean_object* v___y_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Fin_cases___redArg(v___y_350_, v___f_351_, v___y_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_frameLabel___lam__1___boxed(lean_object* v___y_354_, lean_object* v___f_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = lp_Tiling_StickPolyhex_frameLabel___lam__1(v___y_354_, v___f_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec(v___y_354_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_frameLabel(lean_object* v_n_371_, lean_object* v_i_372_, lean_object* v_f_373_){
_start:
{
lean_object* v___f_374_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___x_388_; uint8_t v___x_389_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; uint8_t v___x_401_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___y_424_; 
v___f_374_ = ((lean_object*)(lp_Tiling_StickPolyhex_frameLabel___closed__0));
v___x_388_ = lean_unsigned_to_nat(1u);
v___x_389_ = lean_nat_dec_eq(v_i_372_, v___x_388_);
v___x_401_ = lean_nat_dec_eq(v_i_372_, v_n_371_);
if (v___x_389_ == 0)
{
lean_object* v___x_429_; 
v___x_429_ = lean_box(0);
v___y_424_ = v___x_429_;
goto v___jp_423_;
}
else
{
lean_object* v___x_430_; 
v___x_430_ = ((lean_object*)(lp_Tiling_StickPolyhex_frameLabel___closed__6));
v___y_424_ = v___x_430_;
goto v___jp_423_;
}
v___jp_375_:
{
lean_object* v___f_382_; lean_object* v___f_383_; lean_object* v___f_384_; lean_object* v___f_385_; lean_object* v___f_386_; lean_object* v___x_387_; 
v___f_382_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_frameLabel___lam__1___boxed), 3, 2);
lean_closure_set(v___f_382_, 0, v___y_381_);
lean_closure_set(v___f_382_, 1, v___f_374_);
v___f_383_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_frameLabel___lam__1___boxed), 3, 2);
lean_closure_set(v___f_383_, 0, v___y_377_);
lean_closure_set(v___f_383_, 1, v___f_382_);
lean_inc(v___y_379_);
v___f_384_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_frameLabel___lam__1___boxed), 3, 2);
lean_closure_set(v___f_384_, 0, v___y_379_);
lean_closure_set(v___f_384_, 1, v___f_383_);
v___f_385_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_frameLabel___lam__1___boxed), 3, 2);
lean_closure_set(v___f_385_, 0, v___y_378_);
lean_closure_set(v___f_385_, 1, v___f_384_);
v___f_386_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_frameLabel___lam__1___boxed), 3, 2);
lean_closure_set(v___f_386_, 0, v___y_376_);
lean_closure_set(v___f_386_, 1, v___f_385_);
v___x_387_ = l_Fin_cases___redArg(v___y_380_, v___f_386_, v_f_373_);
return v___x_387_;
}
v___jp_390_:
{
if (v___x_389_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_396_ = lean_nat_add(v_n_371_, v___x_388_);
v___x_397_ = lean_nat_sub(v___x_396_, v_i_372_);
lean_dec(v_i_372_);
lean_dec(v___x_396_);
v___x_398_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
v___x_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
v___y_376_ = v___y_391_;
v___y_377_ = v___y_395_;
v___y_378_ = v___y_392_;
v___y_379_ = v___y_393_;
v___y_380_ = v___y_394_;
v___y_381_ = v___x_399_;
goto v___jp_375_;
}
else
{
lean_object* v___x_400_; 
lean_dec(v_i_372_);
v___x_400_ = ((lean_object*)(lp_Tiling_StickPolyhex_frameLabel___closed__1));
v___y_376_ = v___y_391_;
v___y_377_ = v___y_395_;
v___y_378_ = v___y_392_;
v___y_379_ = v___y_393_;
v___y_380_ = v___y_394_;
v___y_381_ = v___x_400_;
goto v___jp_375_;
}
}
v___jp_402_:
{
if (v___x_401_ == 0)
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_407_ = lean_nat_sub(v_n_371_, v_i_372_);
v___x_408_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
v___x_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
v___y_391_ = v___y_403_;
v___y_392_ = v___y_404_;
v___y_393_ = v___y_406_;
v___y_394_ = v___y_405_;
v___y_395_ = v___x_409_;
goto v___jp_390_;
}
else
{
lean_object* v___x_410_; 
v___x_410_ = ((lean_object*)(lp_Tiling_StickPolyhex_frameLabel___closed__2));
v___y_391_ = v___y_403_;
v___y_392_ = v___y_404_;
v___y_393_ = v___y_406_;
v___y_394_ = v___y_405_;
v___y_395_ = v___x_410_;
goto v___jp_390_;
}
}
v___jp_411_:
{
if (v___x_401_ == 0)
{
lean_object* v___x_415_; 
v___x_415_ = lean_box(0);
v___y_403_ = v___y_412_;
v___y_404_ = v___y_414_;
v___y_405_ = v___y_413_;
v___y_406_ = v___x_415_;
goto v___jp_402_;
}
else
{
lean_object* v___x_416_; 
v___x_416_ = ((lean_object*)(lp_Tiling_StickPolyhex_frameLabel___closed__3));
v___y_403_ = v___y_412_;
v___y_404_ = v___y_414_;
v___y_405_ = v___y_413_;
v___y_406_ = v___x_416_;
goto v___jp_402_;
}
}
v___jp_417_:
{
if (v___x_401_ == 0)
{
lean_object* v___x_420_; lean_object* v___x_421_; 
lean_inc(v_i_372_);
v___x_420_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_420_, 0, v_i_372_);
v___x_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
v___y_412_ = v___y_419_;
v___y_413_ = v___y_418_;
v___y_414_ = v___x_421_;
goto v___jp_411_;
}
else
{
lean_object* v___x_422_; 
v___x_422_ = ((lean_object*)(lp_Tiling_StickPolyhex_frameLabel___closed__4));
v___y_412_ = v___y_419_;
v___y_413_ = v___y_418_;
v___y_414_ = v___x_422_;
goto v___jp_411_;
}
}
v___jp_423_:
{
if (v___x_389_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_425_ = lean_nat_sub(v_i_372_, v___x_388_);
v___x_426_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
v___x_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
v___y_418_ = v___y_424_;
v___y_419_ = v___x_427_;
goto v___jp_417_;
}
else
{
lean_object* v___x_428_; 
v___x_428_ = ((lean_object*)(lp_Tiling_StickPolyhex_frameLabel___closed__5));
v___y_418_ = v___y_424_;
v___y_419_ = v___x_428_;
goto v___jp_417_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_frameLabel___boxed(lean_object* v_n_431_, lean_object* v_i_432_, lean_object* v_f_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = lp_Tiling_StickPolyhex_frameLabel(v_n_431_, v_i_432_, v_f_433_);
lean_dec(v_f_433_);
lean_dec(v_n_431_);
return v_res_434_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_StickTiling_labelOf___redArg___closed__0(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_unsigned_to_nat(6u);
v___x_436_ = lp_mathlib_ZMod_commRing(v___x_435_);
return v___x_436_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_StickTiling_labelOf___redArg___closed__1(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_obj_once(&lp_Tiling_StickPolyhex_StickTiling_labelOf___redArg___closed__0, &lp_Tiling_StickPolyhex_StickTiling_labelOf___redArg___closed__0_once, _init_lp_Tiling_StickPolyhex_StickTiling_labelOf___redArg___closed__0);
v___x_438_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v___x_437_);
return v___x_438_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_StickTiling_labelOf___redArg___closed__2(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = lean_obj_once(&lp_Tiling_StickPolyhex_StickTiling_labelOf___redArg___closed__1, &lp_Tiling_StickPolyhex_StickTiling_labelOf___redArg___closed__1_once, _init_lp_Tiling_StickPolyhex_StickTiling_labelOf___redArg___closed__1);
v___x_440_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_labelOf___redArg(lean_object* v_T_441_, lean_object* v_R_442_, lean_object* v_c_443_, lean_object* v_e_444_){
_start:
{
lean_object* v_dir_445_; lean_object* v_idx_446_; lean_object* v___x_447_; lean_object* v_toSemiring_448_; lean_object* v___x_449_; lean_object* v_toAdd_450_; lean_object* v___x_451_; lean_object* v_toSub_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v_dir_445_ = lean_ctor_get(v_T_441_, 0);
lean_inc_ref(v_dir_445_);
v_idx_446_ = lean_ctor_get(v_T_441_, 1);
lean_inc_ref(v_idx_446_);
lean_dec_ref(v_T_441_);
v___x_447_ = lean_obj_once(&lp_Tiling_StickPolyhex_StickTiling_labelOf___redArg___closed__0, &lp_Tiling_StickPolyhex_StickTiling_labelOf___redArg___closed__0_once, _init_lp_Tiling_StickPolyhex_StickTiling_labelOf___redArg___closed__0);
v_toSemiring_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc_ref(v_toSemiring_448_);
v___x_449_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_448_);
v_toAdd_450_ = lean_ctor_get(v___x_449_, 1);
lean_inc(v_toAdd_450_);
lean_dec_ref(v___x_449_);
v___x_451_ = lean_obj_once(&lp_Tiling_StickPolyhex_StickTiling_labelOf___redArg___closed__2, &lp_Tiling_StickPolyhex_StickTiling_labelOf___redArg___closed__2_once, _init_lp_Tiling_StickPolyhex_StickTiling_labelOf___redArg___closed__2);
v_toSub_452_ = lean_ctor_get(v___x_451_, 2);
lean_inc_ref(v_c_443_);
v___x_453_ = lean_apply_1(v_idx_446_, v_c_443_);
v___x_454_ = lean_apply_1(v_dir_445_, v_c_443_);
lean_inc(v_toSub_452_);
v___x_455_ = lean_apply_2(v_toSub_452_, v_e_444_, v___x_454_);
v___x_456_ = lp_Tiling_StickPolyhex_HexDir_W;
v___x_457_ = lean_apply_2(v_toAdd_450_, v___x_455_, v___x_456_);
v___x_458_ = lean_apply_2(v_R_442_, v___x_453_, v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_labelOf(lean_object* v_n_459_, lean_object* v_T_460_, lean_object* v_R_461_, lean_object* v_c_462_, lean_object* v_e_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = lp_Tiling_StickPolyhex_StickTiling_labelOf___redArg(v_T_460_, v_R_461_, v_c_462_, v_e_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_StickTiling_labelOf___boxed(lean_object* v_n_465_, lean_object* v_T_466_, lean_object* v_R_467_, lean_object* v_c_468_, lean_object* v_e_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = lp_Tiling_StickPolyhex_StickTiling_labelOf(v_n_465_, v_T_466_, v_R_467_, v_c_468_, v_e_469_);
lean_dec(v_n_465_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_markedRules___redArg(lean_object* v_n_471_){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = lean_unsigned_to_nat(1u);
v___x_473_ = lean_nat_add(v_n_471_, v___x_472_);
v___x_474_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_frameLabel___boxed), 3, 1);
lean_closure_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_markedRules___redArg___boxed(lean_object* v_n_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = lp_Tiling_StickPolyhex_markedRules___redArg(v_n_475_);
lean_dec(v_n_475_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_markedRules(lean_object* v_n_477_, lean_object* v_M_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = lp_Tiling_StickPolyhex_markedRules___redArg(v_n_477_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_markedRules___boxed(lean_object* v_n_480_, lean_object* v_M_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = lp_Tiling_StickPolyhex_markedRules(v_n_480_, v_M_481_);
lean_dec(v_n_480_);
return v_res_482_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_MainResults_HexGrid(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_MainResults_StickDefinitions(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_MainResults_HexGrid(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
