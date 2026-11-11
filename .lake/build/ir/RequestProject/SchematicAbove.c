// Lean compiler output
// Module: RequestProject.SchematicAbove
// Imports: public import Init public meta import Init public import RequestProject.SchematicStackSets public import RequestProject.SchematicRows
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
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lp_RequestProject_StickPolyhex_shearCell(lean_object*, lean_object*);
static lean_once_cell_t lp_RequestProject_StickPolyhex_Schematic_gcell___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_RequestProject_StickPolyhex_Schematic_gcell___redArg___closed__0;
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_gcell___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_gcell___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_gcell(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_gcell___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_RequestProject_StickPolyhex_Schematic_gcell___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_gcell___redArg(lean_object* v_n_3_, lean_object* v_y_4_, lean_object* v_r_5_, lean_object* v_i_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_7_ = lean_nat_to_int(v_n_3_);
v___x_8_ = lean_obj_once(&lp_RequestProject_StickPolyhex_Schematic_gcell___redArg___closed__0, &lp_RequestProject_StickPolyhex_Schematic_gcell___redArg___closed__0_once, _init_lp_RequestProject_StickPolyhex_Schematic_gcell___redArg___closed__0);
v___x_9_ = lean_int_add(v___x_7_, v___x_8_);
lean_dec(v___x_7_);
v___x_10_ = lean_int_mul(v___x_9_, v_r_5_);
lean_dec(v___x_9_);
v___x_11_ = lean_int_add(v___x_10_, v_i_6_);
lean_dec(v___x_10_);
v___x_12_ = lp_RequestProject_StickPolyhex_shearCell(v_y_4_, v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_gcell___redArg___boxed(lean_object* v_n_13_, lean_object* v_y_14_, lean_object* v_r_15_, lean_object* v_i_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_RequestProject_StickPolyhex_Schematic_gcell___redArg(v_n_13_, v_y_14_, v_r_15_, v_i_16_);
lean_dec(v_i_16_);
lean_dec(v_r_15_);
lean_dec(v_y_14_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_gcell(lean_object* v_n_18_, lean_object* v___S_19_, lean_object* v_y_20_, lean_object* v_r_21_, lean_object* v_i_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lp_RequestProject_StickPolyhex_Schematic_gcell___redArg(v_n_18_, v_y_20_, v_r_21_, v_i_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_StickPolyhex_Schematic_gcell___boxed(lean_object* v_n_24_, lean_object* v___S_25_, lean_object* v_y_26_, lean_object* v_r_27_, lean_object* v_i_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lp_RequestProject_StickPolyhex_Schematic_gcell(v_n_24_, v___S_25_, v_y_26_, v_r_27_, v_i_28_);
lean_dec(v_i_28_);
lean_dec(v_r_27_);
lean_dec(v_y_26_);
lean_dec_ref(v___S_25_);
return v_res_29_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_SchematicStackSets(uint8_t builtin);
lean_object* initialize_RequestProject_RequestProject_SchematicRows(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_SchematicAbove(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_SchematicStackSets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RequestProject_RequestProject_SchematicRows(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
