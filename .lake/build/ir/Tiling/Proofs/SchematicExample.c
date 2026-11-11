// Lean compiler output
// Module: Tiling.Proofs.SchematicExample
// Imports: public import Init public meta import Init public import Tiling.Proofs.MarkedTiling public import Tiling.Proofs.SchematicWeave
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
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
static lean_once_cell_t lp_Tiling___private_Tiling_Proofs_SchematicExample_0__StickPolyhex_Schematic_perSlot___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling___private_Tiling_Proofs_SchematicExample_0__StickPolyhex_Schematic_perSlot___closed__0;
LEAN_EXPORT lean_object* lp_Tiling___private_Tiling_Proofs_SchematicExample_0__StickPolyhex_Schematic_perSlot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling___private_Tiling_Proofs_SchematicExample_0__StickPolyhex_Schematic_perSlot___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_Tiling_StickPolyhex_Schematic_periodic___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Tiling_StickPolyhex_Schematic_periodic___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Schematic_periodic___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Schematic_periodic___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Schematic_periodic___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Schematic_periodic(lean_object*, lean_object*);
static lean_object* _init_lp_Tiling___private_Tiling_Proofs_SchematicExample_0__StickPolyhex_Schematic_perSlot___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_Tiling___private_Tiling_Proofs_SchematicExample_0__StickPolyhex_Schematic_perSlot(lean_object* v_n_3_, lean_object* v_m_4_){
_start:
{
lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_5_ = lean_nat_to_int(v_n_3_);
v___x_6_ = lean_int_dec_le(v_m_4_, v___x_5_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; lean_object* v___x_8_; uint8_t v___x_9_; 
v___x_7_ = lean_obj_once(&lp_Tiling___private_Tiling_Proofs_SchematicExample_0__StickPolyhex_Schematic_perSlot___closed__0, &lp_Tiling___private_Tiling_Proofs_SchematicExample_0__StickPolyhex_Schematic_perSlot___closed__0_once, _init_lp_Tiling___private_Tiling_Proofs_SchematicExample_0__StickPolyhex_Schematic_perSlot___closed__0);
v___x_8_ = lean_int_add(v___x_5_, v___x_7_);
lean_dec(v___x_5_);
v___x_9_ = lean_int_dec_eq(v_m_4_, v___x_8_);
lean_dec(v___x_8_);
if (v___x_9_ == 0)
{
lean_object* v___x_10_; 
v___x_10_ = lean_box(2);
return v___x_10_;
}
else
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(1);
return v___x_11_;
}
}
else
{
lean_object* v___x_12_; lean_object* v___x_13_; 
lean_dec(v___x_5_);
v___x_12_ = l_Int_toNat(v_m_4_);
v___x_13_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* lp_Tiling___private_Tiling_Proofs_SchematicExample_0__StickPolyhex_Schematic_perSlot___boxed(lean_object* v_n_14_, lean_object* v_m_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_Tiling___private_Tiling_Proofs_SchematicExample_0__StickPolyhex_Schematic_perSlot(v_n_14_, v_m_15_);
lean_dec(v_m_15_);
return v_res_16_;
}
}
static lean_object* _init_lp_Tiling_StickPolyhex_Schematic_periodic___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = lean_unsigned_to_nat(3u);
v___x_18_ = lean_nat_to_int(v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Schematic_periodic___redArg___lam__0(lean_object* v_n_19_, lean_object* v_r_20_, lean_object* v_x_21_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_22_ = lean_obj_once(&lp_Tiling_StickPolyhex_Schematic_periodic___redArg___lam__0___closed__0, &lp_Tiling_StickPolyhex_Schematic_periodic___redArg___lam__0___closed__0_once, _init_lp_Tiling_StickPolyhex_Schematic_periodic___redArg___lam__0___closed__0);
v___x_23_ = lean_int_mul(v___x_22_, v_r_20_);
v___x_24_ = lean_int_add(v_x_21_, v___x_23_);
lean_dec(v___x_23_);
lean_inc(v_n_19_);
v___x_25_ = lean_nat_to_int(v_n_19_);
v___x_26_ = lean_int_add(v___x_25_, v___x_22_);
lean_dec(v___x_25_);
v___x_27_ = lean_int_emod(v___x_24_, v___x_26_);
lean_dec(v___x_26_);
lean_dec(v___x_24_);
v___x_28_ = lp_Tiling___private_Tiling_Proofs_SchematicExample_0__StickPolyhex_Schematic_perSlot(v_n_19_, v___x_27_);
lean_dec(v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Schematic_periodic___redArg___lam__0___boxed(lean_object* v_n_29_, lean_object* v_r_30_, lean_object* v_x_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_Tiling_StickPolyhex_Schematic_periodic___redArg___lam__0(v_n_29_, v_r_30_, v_x_31_);
lean_dec(v_x_31_);
lean_dec(v_r_30_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Schematic_periodic___redArg(lean_object* v_n_33_){
_start:
{
lean_object* v___f_34_; 
v___f_34_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_Schematic_periodic___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_34_, 0, v_n_33_);
return v___f_34_;
}
}
LEAN_EXPORT lean_object* lp_Tiling_StickPolyhex_Schematic_periodic(lean_object* v_n_35_, lean_object* v_hn_36_){
_start:
{
lean_object* v___f_37_; 
v___f_37_ = lean_alloc_closure((void*)(lp_Tiling_StickPolyhex_Schematic_periodic___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_37_, 0, v_n_35_);
return v___f_37_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_MarkedTiling(uint8_t builtin);
lean_object* initialize_Tiling_Tiling_Proofs_SchematicWeave(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tiling_Tiling_Proofs_SchematicExample(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_MarkedTiling(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tiling_Tiling_Proofs_SchematicWeave(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
