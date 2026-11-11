// Lean compiler output
// Module: Tiling.MainResults.ABTiling
// Imports: public import Init public meta import Init public import LeanWang.Basic
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
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
extern lean_object* lp_mathlib_Nat_encodable;
lean_object* lp_mathlib_Encodable_Prod_encodable___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Encodable_ofEquiv___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_List_encodable___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lp_mathlib_Int_instDecidablePredEven(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t l_instDecidableEqList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_Tiling_Tiling_AB_instDecidableEqABTile_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_instDecidableEqABTile_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_Tiling_Tiling_AB_instDecidableEqABTile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_instDecidableEqABTile___boxed(lean_object*, lean_object*);
static const lean_string_object lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__0 = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__0_value;
static const lean_string_object lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ul"};
static const lean_object* lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__1 = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__1_value;
static const lean_ctor_object lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__1_value)}};
static const lean_object* lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__2 = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__2_value;
static const lean_ctor_object lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__2_value)}};
static const lean_object* lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__3 = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__3_value;
static const lean_string_object lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__4 = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__4_value;
static const lean_ctor_object lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__4_value)}};
static const lean_object* lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__5 = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__5_value;
static const lean_ctor_object lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__3_value),((lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__5_value)}};
static const lean_object* lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__6 = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__6_value;
static lean_once_cell_t lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__7;
static const lean_string_object lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__8 = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__8_value;
static const lean_ctor_object lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__8_value)}};
static const lean_object* lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__9 = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__9_value;
static const lean_string_object lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ur"};
static const lean_object* lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__10 = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__10_value;
static const lean_ctor_object lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__10_value)}};
static const lean_object* lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__11 = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__11_value;
static const lean_string_object lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ll"};
static const lean_object* lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__12 = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__12_value;
static const lean_ctor_object lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__12_value)}};
static const lean_object* lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__13 = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__13_value;
static const lean_string_object lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lr"};
static const lean_object* lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__14 = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__14_value;
static const lean_ctor_object lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__14_value)}};
static const lean_object* lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__15 = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__15_value;
static const lean_string_object lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__16 = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__16_value;
static lean_once_cell_t lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__17;
static lean_once_cell_t lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__18;
static const lean_ctor_object lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__0_value)}};
static const lean_object* lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__19 = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__19_value;
static const lean_ctor_object lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__16_value)}};
static const lean_object* lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__20 = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__20_value;
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_instReprABTile_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_instReprABTile_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_instReprABTile_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_Tiling_Tiling_AB_instReprABTile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Tiling_Tiling_AB_instReprABTile_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Tiling_Tiling_AB_instReprABTile___closed__0 = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTile___closed__0_value;
LEAN_EXPORT const lean_object* lp_Tiling_Tiling_AB_instReprABTile = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTile___closed__0_value;
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_ABTile_toTuple(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_ABTile_toTuple___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_ABTile_ofTuple(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_ABTile_ofTuple___boxed(lean_object*);
static const lean_closure_object lp_Tiling_Tiling_AB_ABTile_equivTuple___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Tiling_Tiling_AB_ABTile_toTuple___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Tiling_Tiling_AB_ABTile_equivTuple___closed__0 = (const lean_object*)&lp_Tiling_Tiling_AB_ABTile_equivTuple___closed__0_value;
static const lean_closure_object lp_Tiling_Tiling_AB_ABTile_equivTuple___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Tiling_Tiling_AB_ABTile_ofTuple___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Tiling_Tiling_AB_ABTile_equivTuple___closed__1 = (const lean_object*)&lp_Tiling_Tiling_AB_ABTile_equivTuple___closed__1_value;
static const lean_ctor_object lp_Tiling_Tiling_AB_ABTile_equivTuple___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_Tiling_Tiling_AB_ABTile_equivTuple___closed__0_value),((lean_object*)&lp_Tiling_Tiling_AB_ABTile_equivTuple___closed__1_value)}};
static const lean_object* lp_Tiling_Tiling_AB_ABTile_equivTuple___closed__2 = (const lean_object*)&lp_Tiling_Tiling_AB_ABTile_equivTuple___closed__2_value;
LEAN_EXPORT const lean_object* lp_Tiling_Tiling_AB_ABTile_equivTuple = (const lean_object*)&lp_Tiling_Tiling_AB_ABTile_equivTuple___closed__2_value;
static lean_once_cell_t lp_Tiling_Tiling_AB_instPrimcodableABTile___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_Tiling_AB_instPrimcodableABTile___closed__0;
static lean_once_cell_t lp_Tiling_Tiling_AB_instPrimcodableABTile___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_Tiling_AB_instPrimcodableABTile___closed__1;
static lean_once_cell_t lp_Tiling_Tiling_AB_instPrimcodableABTile___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_Tiling_AB_instPrimcodableABTile___closed__2;
static lean_once_cell_t lp_Tiling_Tiling_AB_instPrimcodableABTile___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_Tiling_AB_instPrimcodableABTile___closed__3;
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_instPrimcodableABTile;
LEAN_EXPORT uint8_t lp_Tiling_Tiling_AB_instDecidableEqABTileSet_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_instDecidableEqABTileSet_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_Tiling_Tiling_AB_instDecidableEqABTileSet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_instDecidableEqABTileSet___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_Std_Format_joinSep___at___00List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__0 = (const lean_object*)&lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__0_value;
static const lean_ctor_object lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__1 = (const lean_object*)&lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__1_value;
static const lean_string_object lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__2 = (const lean_object*)&lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__2_value;
static const lean_ctor_object lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__3 = (const lean_object*)&lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__3_value;
static const lean_string_object lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__4 = (const lean_object*)&lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__4_value;
static lean_once_cell_t lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__5;
static lean_once_cell_t lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__6;
static const lean_ctor_object lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__2_value)}};
static const lean_object* lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__7 = (const lean_object*)&lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__7_value;
static const lean_ctor_object lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__4_value)}};
static const lean_object* lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__8 = (const lean_object*)&lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__8_value;
LEAN_EXPORT lean_object* lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg(lean_object*);
static const lean_string_object lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "A"};
static const lean_object* lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__0 = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__0_value;
static const lean_ctor_object lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__0_value)}};
static const lean_object* lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__1 = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__1_value;
static const lean_ctor_object lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__1_value)}};
static const lean_object* lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__2 = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__2_value;
static const lean_ctor_object lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__2_value),((lean_object*)&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__5_value)}};
static const lean_object* lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__3 = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__3_value;
static lean_once_cell_t lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__4;
static const lean_string_object lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "B"};
static const lean_object* lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__5 = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__5_value;
static const lean_ctor_object lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__5_value)}};
static const lean_object* lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__6 = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__6_value;
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_instReprABTileSet_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_instReprABTileSet_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_Tiling_Tiling_AB_instReprABTileSet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Tiling_Tiling_AB_instReprABTileSet_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Tiling_Tiling_AB_instReprABTileSet___closed__0 = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTileSet___closed__0_value;
LEAN_EXPORT const lean_object* lp_Tiling_Tiling_AB_instReprABTileSet = (const lean_object*)&lp_Tiling_Tiling_AB_instReprABTileSet___closed__0_value;
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_ABTileSet_equivProd___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_ABTileSet_equivProd___lam__1(lean_object*);
static const lean_closure_object lp_Tiling_Tiling_AB_ABTileSet_equivProd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Tiling_Tiling_AB_ABTileSet_equivProd___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Tiling_Tiling_AB_ABTileSet_equivProd___closed__0 = (const lean_object*)&lp_Tiling_Tiling_AB_ABTileSet_equivProd___closed__0_value;
static const lean_closure_object lp_Tiling_Tiling_AB_ABTileSet_equivProd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Tiling_Tiling_AB_ABTileSet_equivProd___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Tiling_Tiling_AB_ABTileSet_equivProd___closed__1 = (const lean_object*)&lp_Tiling_Tiling_AB_ABTileSet_equivProd___closed__1_value;
static const lean_ctor_object lp_Tiling_Tiling_AB_ABTileSet_equivProd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_Tiling_Tiling_AB_ABTileSet_equivProd___closed__0_value),((lean_object*)&lp_Tiling_Tiling_AB_ABTileSet_equivProd___closed__1_value)}};
static const lean_object* lp_Tiling_Tiling_AB_ABTileSet_equivProd___closed__2 = (const lean_object*)&lp_Tiling_Tiling_AB_ABTileSet_equivProd___closed__2_value;
LEAN_EXPORT const lean_object* lp_Tiling_Tiling_AB_ABTileSet_equivProd = (const lean_object*)&lp_Tiling_Tiling_AB_ABTileSet_equivProd___closed__2_value;
static lean_once_cell_t lp_Tiling_Tiling_AB_instPrimcodableABTileSet___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_Tiling_AB_instPrimcodableABTileSet___closed__0;
static lean_once_cell_t lp_Tiling_Tiling_AB_instPrimcodableABTileSet___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_Tiling_AB_instPrimcodableABTileSet___closed__1;
static lean_once_cell_t lp_Tiling_Tiling_AB_instPrimcodableABTileSet___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_Tiling_AB_instPrimcodableABTileSet___closed__2;
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_instPrimcodableABTileSet;
static lean_once_cell_t lp_Tiling_Tiling_AB_tileHeight___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_Tiling_AB_tileHeight___closed__0;
static lean_once_cell_t lp_Tiling_Tiling_AB_tileHeight___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_Tiling_AB_tileHeight___closed__1;
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_tileHeight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_tileHeight___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_Tiling_Tiling_AB_instDecidableEqABTile_decEq(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_ul_3_; lean_object* v_ur_4_; lean_object* v_ll_5_; lean_object* v_lr_6_; lean_object* v_ul_7_; lean_object* v_ur_8_; lean_object* v_ll_9_; lean_object* v_lr_10_; uint8_t v___x_11_; 
v_ul_3_ = lean_ctor_get(v_x_1_, 0);
v_ur_4_ = lean_ctor_get(v_x_1_, 1);
v_ll_5_ = lean_ctor_get(v_x_1_, 2);
v_lr_6_ = lean_ctor_get(v_x_1_, 3);
v_ul_7_ = lean_ctor_get(v_x_2_, 0);
v_ur_8_ = lean_ctor_get(v_x_2_, 1);
v_ll_9_ = lean_ctor_get(v_x_2_, 2);
v_lr_10_ = lean_ctor_get(v_x_2_, 3);
v___x_11_ = lean_nat_dec_eq(v_ul_3_, v_ul_7_);
if (v___x_11_ == 0)
{
return v___x_11_;
}
else
{
uint8_t v___x_12_; 
v___x_12_ = lean_nat_dec_eq(v_ur_4_, v_ur_8_);
if (v___x_12_ == 0)
{
return v___x_12_;
}
else
{
uint8_t v___x_13_; 
v___x_13_ = lean_nat_dec_eq(v_ll_5_, v_ll_9_);
if (v___x_13_ == 0)
{
return v___x_13_;
}
else
{
uint8_t v___x_14_; 
v___x_14_ = lean_nat_dec_eq(v_lr_6_, v_lr_10_);
return v___x_14_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_instDecidableEqABTile_decEq___boxed(lean_object* v_x_15_, lean_object* v_x_16_){
_start:
{
uint8_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = lp_Tiling_Tiling_AB_instDecidableEqABTile_decEq(v_x_15_, v_x_16_);
lean_dec_ref(v_x_16_);
lean_dec_ref(v_x_15_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT uint8_t lp_Tiling_Tiling_AB_instDecidableEqABTile(lean_object* v_x_19_, lean_object* v_x_20_){
_start:
{
uint8_t v___x_21_; 
v___x_21_ = lp_Tiling_Tiling_AB_instDecidableEqABTile_decEq(v_x_19_, v_x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_instDecidableEqABTile___boxed(lean_object* v_x_22_, lean_object* v_x_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = lp_Tiling_Tiling_AB_instDecidableEqABTile(v_x_22_, v_x_23_);
lean_dec_ref(v_x_23_);
lean_dec_ref(v_x_22_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
static lean_object* _init_lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = lean_unsigned_to_nat(6u);
v___x_40_ = lean_nat_to_int(v___x_39_);
return v___x_40_;
}
}
static lean_object* _init_lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = ((lean_object*)(lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__0));
v___x_55_ = lean_string_length(v___x_54_);
return v___x_55_;
}
}
static lean_object* _init_lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_obj_once(&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__17, &lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__17_once, _init_lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__17);
v___x_57_ = lean_nat_to_int(v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_instReprABTile_repr___redArg(lean_object* v_x_62_){
_start:
{
lean_object* v_ul_63_; lean_object* v_ur_64_; lean_object* v_ll_65_; lean_object* v_lr_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; uint8_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v_ul_63_ = lean_ctor_get(v_x_62_, 0);
lean_inc(v_ul_63_);
v_ur_64_ = lean_ctor_get(v_x_62_, 1);
lean_inc(v_ur_64_);
v_ll_65_ = lean_ctor_get(v_x_62_, 2);
lean_inc(v_ll_65_);
v_lr_66_ = lean_ctor_get(v_x_62_, 3);
lean_inc(v_lr_66_);
lean_dec_ref(v_x_62_);
v___x_67_ = ((lean_object*)(lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__5));
v___x_68_ = ((lean_object*)(lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__6));
v___x_69_ = lean_obj_once(&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__7, &lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__7_once, _init_lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__7);
v___x_70_ = l_Nat_reprFast(v_ul_63_);
v___x_71_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
v___x_72_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_69_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
v___x_73_ = 0;
v___x_74_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_74_, 0, v___x_72_);
lean_ctor_set_uint8(v___x_74_, sizeof(void*)*1, v___x_73_);
v___x_75_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_68_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = ((lean_object*)(lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__9));
v___x_77_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_75_);
lean_ctor_set(v___x_77_, 1, v___x_76_);
v___x_78_ = lean_box(1);
v___x_79_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_77_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v___x_80_ = ((lean_object*)(lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__11));
v___x_81_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_79_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
v___x_82_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set(v___x_82_, 1, v___x_67_);
v___x_83_ = l_Nat_reprFast(v_ur_64_);
v___x_84_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
v___x_85_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_69_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*1, v___x_73_);
v___x_87_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_82_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v___x_76_);
v___x_89_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set(v___x_89_, 1, v___x_78_);
v___x_90_ = ((lean_object*)(lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__13));
v___x_91_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
lean_ctor_set(v___x_92_, 1, v___x_67_);
v___x_93_ = l_Nat_reprFast(v_ll_65_);
v___x_94_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
v___x_95_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_69_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
v___x_96_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set_uint8(v___x_96_, sizeof(void*)*1, v___x_73_);
v___x_97_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_92_);
lean_ctor_set(v___x_97_, 1, v___x_96_);
v___x_98_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v___x_76_);
v___x_99_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v___x_78_);
v___x_100_ = ((lean_object*)(lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__15));
v___x_101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_99_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v___x_102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v___x_67_);
v___x_103_ = l_Nat_reprFast(v_lr_66_);
v___x_104_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
v___x_105_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_69_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
v___x_106_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set_uint8(v___x_106_, sizeof(void*)*1, v___x_73_);
v___x_107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_102_);
lean_ctor_set(v___x_107_, 1, v___x_106_);
v___x_108_ = lean_obj_once(&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__18, &lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__18_once, _init_lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__18);
v___x_109_ = ((lean_object*)(lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__19));
v___x_110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
lean_ctor_set(v___x_110_, 1, v___x_107_);
v___x_111_ = ((lean_object*)(lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__20));
v___x_112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_110_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
v___x_113_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_108_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
v___x_114_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set_uint8(v___x_114_, sizeof(void*)*1, v___x_73_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_instReprABTile_repr(lean_object* v_x_115_, lean_object* v_prec_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = lp_Tiling_Tiling_AB_instReprABTile_repr___redArg(v_x_115_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_instReprABTile_repr___boxed(lean_object* v_x_118_, lean_object* v_prec_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = lp_Tiling_Tiling_AB_instReprABTile_repr(v_x_118_, v_prec_119_);
lean_dec(v_prec_119_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_ABTile_toTuple(lean_object* v_t_123_){
_start:
{
lean_object* v_ul_124_; lean_object* v_ur_125_; lean_object* v_ll_126_; lean_object* v_lr_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v_ul_124_ = lean_ctor_get(v_t_123_, 0);
v_ur_125_ = lean_ctor_get(v_t_123_, 1);
v_ll_126_ = lean_ctor_get(v_t_123_, 2);
v_lr_127_ = lean_ctor_get(v_t_123_, 3);
lean_inc(v_lr_127_);
lean_inc(v_ll_126_);
v___x_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_128_, 0, v_ll_126_);
lean_ctor_set(v___x_128_, 1, v_lr_127_);
lean_inc(v_ur_125_);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v_ur_125_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
lean_inc(v_ul_124_);
v___x_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_130_, 0, v_ul_124_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_ABTile_toTuple___boxed(lean_object* v_t_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = lp_Tiling_Tiling_AB_ABTile_toTuple(v_t_131_);
lean_dec_ref(v_t_131_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_ABTile_ofTuple(lean_object* v_p_133_){
_start:
{
lean_object* v_snd_134_; lean_object* v_snd_135_; lean_object* v_fst_136_; lean_object* v_fst_137_; lean_object* v_fst_138_; lean_object* v_snd_139_; lean_object* v___x_140_; 
v_snd_134_ = lean_ctor_get(v_p_133_, 1);
v_snd_135_ = lean_ctor_get(v_snd_134_, 1);
v_fst_136_ = lean_ctor_get(v_p_133_, 0);
v_fst_137_ = lean_ctor_get(v_snd_134_, 0);
v_fst_138_ = lean_ctor_get(v_snd_135_, 0);
v_snd_139_ = lean_ctor_get(v_snd_135_, 1);
lean_inc(v_snd_139_);
lean_inc(v_fst_138_);
lean_inc(v_fst_137_);
lean_inc(v_fst_136_);
v___x_140_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_140_, 0, v_fst_136_);
lean_ctor_set(v___x_140_, 1, v_fst_137_);
lean_ctor_set(v___x_140_, 2, v_fst_138_);
lean_ctor_set(v___x_140_, 3, v_snd_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_ABTile_ofTuple___boxed(lean_object* v_p_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = lp_Tiling_Tiling_AB_ABTile_ofTuple(v_p_141_);
lean_dec_ref(v_p_141_);
return v_res_142_;
}
}
static lean_object* _init_lp_Tiling_Tiling_AB_instPrimcodableABTile___closed__0(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = lp_mathlib_Nat_encodable;
v___x_150_ = lp_mathlib_Encodable_Prod_encodable___redArg(v___x_149_, v___x_149_);
return v___x_150_;
}
}
static lean_object* _init_lp_Tiling_Tiling_AB_instPrimcodableABTile___closed__1(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_151_ = lean_obj_once(&lp_Tiling_Tiling_AB_instPrimcodableABTile___closed__0, &lp_Tiling_Tiling_AB_instPrimcodableABTile___closed__0_once, _init_lp_Tiling_Tiling_AB_instPrimcodableABTile___closed__0);
v___x_152_ = lp_mathlib_Nat_encodable;
v___x_153_ = lp_mathlib_Encodable_Prod_encodable___redArg(v___x_152_, v___x_151_);
return v___x_153_;
}
}
static lean_object* _init_lp_Tiling_Tiling_AB_instPrimcodableABTile___closed__2(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_154_ = lean_obj_once(&lp_Tiling_Tiling_AB_instPrimcodableABTile___closed__1, &lp_Tiling_Tiling_AB_instPrimcodableABTile___closed__1_once, _init_lp_Tiling_Tiling_AB_instPrimcodableABTile___closed__1);
v___x_155_ = lp_mathlib_Nat_encodable;
v___x_156_ = lp_mathlib_Encodable_Prod_encodable___redArg(v___x_155_, v___x_154_);
return v___x_156_;
}
}
static lean_object* _init_lp_Tiling_Tiling_AB_instPrimcodableABTile___closed__3(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = ((lean_object*)(lp_Tiling_Tiling_AB_ABTile_equivTuple));
v___x_158_ = lean_obj_once(&lp_Tiling_Tiling_AB_instPrimcodableABTile___closed__2, &lp_Tiling_Tiling_AB_instPrimcodableABTile___closed__2_once, _init_lp_Tiling_Tiling_AB_instPrimcodableABTile___closed__2);
v___x_159_ = lp_mathlib_Encodable_ofEquiv___redArg(v___x_158_, v___x_157_);
return v___x_159_;
}
}
static lean_object* _init_lp_Tiling_Tiling_AB_instPrimcodableABTile(void){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lean_obj_once(&lp_Tiling_Tiling_AB_instPrimcodableABTile___closed__3, &lp_Tiling_Tiling_AB_instPrimcodableABTile___closed__3_once, _init_lp_Tiling_Tiling_AB_instPrimcodableABTile___closed__3);
return v___x_160_;
}
}
LEAN_EXPORT uint8_t lp_Tiling_Tiling_AB_instDecidableEqABTileSet_decEq(lean_object* v_x_161_, lean_object* v_x_162_){
_start:
{
lean_object* v_A_163_; lean_object* v_B_164_; lean_object* v_A_165_; lean_object* v_B_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v_A_163_ = lean_ctor_get(v_x_161_, 0);
lean_inc(v_A_163_);
v_B_164_ = lean_ctor_get(v_x_161_, 1);
lean_inc(v_B_164_);
lean_dec_ref(v_x_161_);
v_A_165_ = lean_ctor_get(v_x_162_, 0);
lean_inc(v_A_165_);
v_B_166_ = lean_ctor_get(v_x_162_, 1);
lean_inc(v_B_166_);
lean_dec_ref(v_x_162_);
v___x_167_ = lean_alloc_closure((void*)(lp_Tiling_Tiling_AB_instDecidableEqABTile___boxed), 2, 0);
lean_inc_ref(v___x_167_);
v___x_168_ = l_instDecidableEqList___redArg(v___x_167_, v_A_163_, v_A_165_);
if (v___x_168_ == 0)
{
lean_dec_ref(v___x_167_);
lean_dec(v_B_166_);
lean_dec(v_B_164_);
return v___x_168_;
}
else
{
uint8_t v___x_169_; 
v___x_169_ = l_instDecidableEqList___redArg(v___x_167_, v_B_164_, v_B_166_);
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_instDecidableEqABTileSet_decEq___boxed(lean_object* v_x_170_, lean_object* v_x_171_){
_start:
{
uint8_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = lp_Tiling_Tiling_AB_instDecidableEqABTileSet_decEq(v_x_170_, v_x_171_);
v_r_173_ = lean_box(v_res_172_);
return v_r_173_;
}
}
LEAN_EXPORT uint8_t lp_Tiling_Tiling_AB_instDecidableEqABTileSet(lean_object* v_x_174_, lean_object* v_x_175_){
_start:
{
uint8_t v___x_176_; 
v___x_176_ = lp_Tiling_Tiling_AB_instDecidableEqABTileSet_decEq(v_x_174_, v_x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_instDecidableEqABTileSet___boxed(lean_object* v_x_177_, lean_object* v_x_178_){
_start:
{
uint8_t v_res_179_; lean_object* v_r_180_; 
v_res_179_ = lp_Tiling_Tiling_AB_instDecidableEqABTileSet(v_x_177_, v_x_178_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_181_, lean_object* v_x_182_, lean_object* v_x_183_){
_start:
{
if (lean_obj_tag(v_x_183_) == 0)
{
lean_dec(v_x_181_);
return v_x_182_;
}
else
{
lean_object* v_head_184_; lean_object* v_tail_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_195_; 
v_head_184_ = lean_ctor_get(v_x_183_, 0);
v_tail_185_ = lean_ctor_get(v_x_183_, 1);
v_isSharedCheck_195_ = !lean_is_exclusive(v_x_183_);
if (v_isSharedCheck_195_ == 0)
{
v___x_187_ = v_x_183_;
v_isShared_188_ = v_isSharedCheck_195_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_tail_185_);
lean_inc(v_head_184_);
lean_dec(v_x_183_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_195_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
lean_inc(v_x_181_);
if (v_isShared_188_ == 0)
{
lean_ctor_set_tag(v___x_187_, 5);
lean_ctor_set(v___x_187_, 1, v_x_181_);
lean_ctor_set(v___x_187_, 0, v_x_182_);
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_x_182_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_x_181_);
v___x_190_ = v_reuseFailAlloc_194_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lp_Tiling_Tiling_AB_instReprABTile_repr___redArg(v_head_184_);
v___x_192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_190_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v_x_182_ = v___x_192_;
v_x_183_ = v_tail_185_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0_spec__0_spec__1(lean_object* v_x_196_, lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
if (lean_obj_tag(v_x_198_) == 0)
{
lean_dec(v_x_196_);
return v_x_197_;
}
else
{
lean_object* v_head_199_; lean_object* v_tail_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_210_; 
v_head_199_ = lean_ctor_get(v_x_198_, 0);
v_tail_200_ = lean_ctor_get(v_x_198_, 1);
v_isSharedCheck_210_ = !lean_is_exclusive(v_x_198_);
if (v_isSharedCheck_210_ == 0)
{
v___x_202_ = v_x_198_;
v_isShared_203_ = v_isSharedCheck_210_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_tail_200_);
lean_inc(v_head_199_);
lean_dec(v_x_198_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_210_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
lean_inc(v_x_196_);
if (v_isShared_203_ == 0)
{
lean_ctor_set_tag(v___x_202_, 5);
lean_ctor_set(v___x_202_, 1, v_x_196_);
lean_ctor_set(v___x_202_, 0, v_x_197_);
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_x_197_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v_x_196_);
v___x_205_ = v_reuseFailAlloc_209_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_206_ = lp_Tiling_Tiling_AB_instReprABTile_repr___redArg(v_head_199_);
v___x_207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_205_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
v___x_208_ = lp_Tiling_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0_spec__0_spec__1_spec__2(v_x_196_, v___x_207_, v_tail_200_);
return v___x_208_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_Std_Format_joinSep___at___00List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0_spec__0(lean_object* v_x_211_, lean_object* v_x_212_){
_start:
{
if (lean_obj_tag(v_x_211_) == 0)
{
lean_object* v___x_213_; 
lean_dec(v_x_212_);
v___x_213_ = lean_box(0);
return v___x_213_;
}
else
{
lean_object* v_tail_214_; 
v_tail_214_ = lean_ctor_get(v_x_211_, 1);
if (lean_obj_tag(v_tail_214_) == 0)
{
lean_object* v_head_215_; lean_object* v___x_216_; 
lean_dec(v_x_212_);
v_head_215_ = lean_ctor_get(v_x_211_, 0);
lean_inc(v_head_215_);
lean_dec_ref_known(v_x_211_, 2);
v___x_216_ = lp_Tiling_Tiling_AB_instReprABTile_repr___redArg(v_head_215_);
return v___x_216_;
}
else
{
lean_object* v_head_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
lean_inc(v_tail_214_);
v_head_217_ = lean_ctor_get(v_x_211_, 0);
lean_inc(v_head_217_);
lean_dec_ref_known(v_x_211_, 2);
v___x_218_ = lp_Tiling_Tiling_AB_instReprABTile_repr___redArg(v_head_217_);
v___x_219_ = lp_Tiling_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0_spec__0_spec__1(v_x_212_, v___x_218_, v_tail_214_);
return v___x_219_;
}
}
}
}
static lean_object* _init_lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = ((lean_object*)(lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__2));
v___x_229_ = lean_string_length(v___x_228_);
return v___x_229_;
}
}
static lean_object* _init_lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_obj_once(&lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__5, &lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__5_once, _init_lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__5);
v___x_231_ = lean_nat_to_int(v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg(lean_object* v_a_236_){
_start:
{
if (lean_obj_tag(v_a_236_) == 0)
{
lean_object* v___x_237_; 
v___x_237_ = ((lean_object*)(lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__1));
return v___x_237_;
}
else
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; lean_object* v___x_247_; 
v___x_238_ = ((lean_object*)(lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__3));
v___x_239_ = lp_Tiling_Std_Format_joinSep___at___00List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0_spec__0(v_a_236_, v___x_238_);
v___x_240_ = lean_obj_once(&lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__6, &lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__6_once, _init_lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__6);
v___x_241_ = ((lean_object*)(lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__7));
v___x_242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v___x_239_);
v___x_243_ = ((lean_object*)(lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg___closed__8));
v___x_244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_242_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_240_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
v___x_246_ = 0;
v___x_247_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_247_, 0, v___x_245_);
lean_ctor_set_uint8(v___x_247_, sizeof(void*)*1, v___x_246_);
return v___x_247_;
}
}
}
static lean_object* _init_lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_unsigned_to_nat(5u);
v___x_258_ = lean_nat_to_int(v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg(lean_object* v_x_262_){
_start:
{
lean_object* v_A_263_; lean_object* v_B_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_296_; 
v_A_263_ = lean_ctor_get(v_x_262_, 0);
v_B_264_ = lean_ctor_get(v_x_262_, 1);
v_isSharedCheck_296_ = !lean_is_exclusive(v_x_262_);
if (v_isSharedCheck_296_ == 0)
{
v___x_266_ = v_x_262_;
v_isShared_267_ = v_isSharedCheck_296_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_B_264_);
lean_inc(v_A_263_);
lean_dec(v_x_262_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_296_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_268_ = ((lean_object*)(lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__5));
v___x_269_ = ((lean_object*)(lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__3));
v___x_270_ = lean_obj_once(&lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__4, &lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__4_once, _init_lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__4);
v___x_271_ = lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg(v_A_263_);
if (v_isShared_267_ == 0)
{
lean_ctor_set_tag(v___x_266_, 4);
lean_ctor_set(v___x_266_, 1, v___x_271_);
lean_ctor_set(v___x_266_, 0, v___x_270_);
v___x_273_ = v___x_266_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_270_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v___x_271_);
v___x_273_ = v_reuseFailAlloc_295_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
uint8_t v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_274_ = 0;
v___x_275_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_275_, 0, v___x_273_);
lean_ctor_set_uint8(v___x_275_, sizeof(void*)*1, v___x_274_);
v___x_276_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_269_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
v___x_277_ = ((lean_object*)(lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__9));
v___x_278_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_276_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = lean_box(1);
v___x_280_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_278_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = ((lean_object*)(lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg___closed__6));
v___x_282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_280_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v___x_268_);
v___x_284_ = lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg(v_B_264_);
v___x_285_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_270_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set_uint8(v___x_286_, sizeof(void*)*1, v___x_274_);
v___x_287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_283_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = lean_obj_once(&lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__18, &lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__18_once, _init_lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__18);
v___x_289_ = ((lean_object*)(lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__19));
v___x_290_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v___x_287_);
v___x_291_ = ((lean_object*)(lp_Tiling_Tiling_AB_instReprABTile_repr___redArg___closed__20));
v___x_292_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_290_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_288_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___x_294_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_294_, 0, v___x_293_);
lean_ctor_set_uint8(v___x_294_, sizeof(void*)*1, v___x_274_);
return v___x_294_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_instReprABTileSet_repr(lean_object* v_x_297_, lean_object* v_prec_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = lp_Tiling_Tiling_AB_instReprABTileSet_repr___redArg(v_x_297_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_instReprABTileSet_repr___boxed(lean_object* v_x_300_, lean_object* v_prec_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = lp_Tiling_Tiling_AB_instReprABTileSet_repr(v_x_300_, v_prec_301_);
lean_dec(v_prec_301_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0(lean_object* v_a_303_, lean_object* v_n_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___redArg(v_a_303_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0___boxed(lean_object* v_a_306_, lean_object* v_n_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = lp_Tiling_List_repr___at___00Tiling_AB_instReprABTileSet_repr_spec__0(v_a_306_, v_n_307_);
lean_dec(v_n_307_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_ABTileSet_equivProd___lam__0(lean_object* v_S_311_){
_start:
{
lean_object* v_A_312_; lean_object* v_B_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
v_A_312_ = lean_ctor_get(v_S_311_, 0);
v_B_313_ = lean_ctor_get(v_S_311_, 1);
v_isSharedCheck_320_ = !lean_is_exclusive(v_S_311_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v_S_311_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_B_313_);
lean_inc(v_A_312_);
lean_dec(v_S_311_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_A_312_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_B_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_ABTileSet_equivProd___lam__1(lean_object* v_p_321_){
_start:
{
lean_object* v_fst_322_; lean_object* v_snd_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_330_; 
v_fst_322_ = lean_ctor_get(v_p_321_, 0);
v_snd_323_ = lean_ctor_get(v_p_321_, 1);
v_isSharedCheck_330_ = !lean_is_exclusive(v_p_321_);
if (v_isSharedCheck_330_ == 0)
{
v___x_325_ = v_p_321_;
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_snd_323_);
lean_inc(v_fst_322_);
lean_dec(v_p_321_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_fst_322_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_snd_323_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
static lean_object* _init_lp_Tiling_Tiling_AB_instPrimcodableABTileSet___closed__0(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lp_Tiling_Tiling_AB_instPrimcodableABTile;
v___x_338_ = lp_mathlib_List_encodable___redArg(v___x_337_);
return v___x_338_;
}
}
static lean_object* _init_lp_Tiling_Tiling_AB_instPrimcodableABTileSet___closed__1(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_obj_once(&lp_Tiling_Tiling_AB_instPrimcodableABTileSet___closed__0, &lp_Tiling_Tiling_AB_instPrimcodableABTileSet___closed__0_once, _init_lp_Tiling_Tiling_AB_instPrimcodableABTileSet___closed__0);
v___x_340_ = lp_mathlib_Encodable_Prod_encodable___redArg(v___x_339_, v___x_339_);
return v___x_340_;
}
}
static lean_object* _init_lp_Tiling_Tiling_AB_instPrimcodableABTileSet___closed__2(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = ((lean_object*)(lp_Tiling_Tiling_AB_ABTileSet_equivProd));
v___x_342_ = lean_obj_once(&lp_Tiling_Tiling_AB_instPrimcodableABTileSet___closed__1, &lp_Tiling_Tiling_AB_instPrimcodableABTileSet___closed__1_once, _init_lp_Tiling_Tiling_AB_instPrimcodableABTileSet___closed__1);
v___x_343_ = lp_mathlib_Encodable_ofEquiv___redArg(v___x_342_, v___x_341_);
return v___x_343_;
}
}
static lean_object* _init_lp_Tiling_Tiling_AB_instPrimcodableABTileSet(void){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = lean_obj_once(&lp_Tiling_Tiling_AB_instPrimcodableABTileSet___closed__2, &lp_Tiling_Tiling_AB_instPrimcodableABTileSet___closed__2_once, _init_lp_Tiling_Tiling_AB_instPrimcodableABTileSet___closed__2);
return v___x_344_;
}
}
static lean_object* _init_lp_Tiling_Tiling_AB_tileHeight___closed__0(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_unsigned_to_nat(2u);
v___x_346_ = lean_nat_to_int(v___x_345_);
return v___x_346_;
}
}
static lean_object* _init_lp_Tiling_Tiling_AB_tileHeight___closed__1(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_unsigned_to_nat(1u);
v___x_348_ = lean_nat_to_int(v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_tileHeight(lean_object* v_x_349_, lean_object* v_k_350_){
_start:
{
uint8_t v___x_351_; 
v___x_351_ = lp_mathlib_Int_instDecidablePredEven(v_x_349_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_352_ = lean_obj_once(&lp_Tiling_Tiling_AB_tileHeight___closed__0, &lp_Tiling_Tiling_AB_tileHeight___closed__0_once, _init_lp_Tiling_Tiling_AB_tileHeight___closed__0);
v___x_353_ = lean_int_mul(v___x_352_, v_k_350_);
v___x_354_ = lean_obj_once(&lp_Tiling_Tiling_AB_tileHeight___closed__1, &lp_Tiling_Tiling_AB_tileHeight___closed__1_once, _init_lp_Tiling_Tiling_AB_tileHeight___closed__1);
v___x_355_ = lean_int_add(v___x_353_, v___x_354_);
lean_dec(v___x_353_);
return v___x_355_;
}
else
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_obj_once(&lp_Tiling_Tiling_AB_tileHeight___closed__0, &lp_Tiling_Tiling_AB_tileHeight___closed__0_once, _init_lp_Tiling_Tiling_AB_tileHeight___closed__0);
v___x_357_ = lean_int_mul(v___x_356_, v_k_350_);
return v___x_357_;
}
}
}
LEAN_EXPORT lean_object* lp_Tiling_Tiling_AB_tileHeight___boxed(lean_object* v_x_358_, lean_object* v_k_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = lp_Tiling_Tiling_AB_tileHeight(v_x_358_, v_k_359_);
lean_dec(v_k_359_);
lean_dec(v_x_358_);
return v_res_360_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_lean__wang_LeanWang_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_MainResults_ABTiling(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__wang_LeanWang_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_Tiling_Tiling_AB_instPrimcodableABTile = _init_lp_Tiling_Tiling_AB_instPrimcodableABTile();
lean_mark_persistent(lp_Tiling_Tiling_AB_instPrimcodableABTile);
lp_Tiling_Tiling_AB_instPrimcodableABTileSet = _init_lp_Tiling_Tiling_AB_instPrimcodableABTileSet();
lean_mark_persistent(lp_Tiling_Tiling_AB_instPrimcodableABTileSet);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
