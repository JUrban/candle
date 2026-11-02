(* ========================================================================== *)
(* Exact ordinary-HOL source identities for the six packed delta shortcuts. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Optimized states are admitted only for the   *)
(* exact compiled polynomial instruction selected by the authenticated       *)
(* source role.  This layer also transports the optimized product jet from   *)
(* its factored analytic presentation to the single polynomial instruction   *)
(* that occurs in the decoded source program.                                 *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_delta_specialized_result_sound.ml";;

module Candle_cv_analytic_expr_packed_source_delta_specialization_sound = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_derivatives;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_packed_source_delta_analytic;;
open Candle_cv_analytic_expr_packed_source_delta_neg_derivative_analytic;;
open Candle_cv_analytic_expr_packed_source_delta_product_analytic;;
open Candle_cv_analytic_expr_packed_source_delta_specialized_result_sound;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;

let candle_packed_delta_product_source_poly_def = new_definition
 `candle_packed_delta_product_source_poly coordinate =
    Candle_poly_mul (Candle_poly_const 4 0 0)
      (Candle_poly_mul (Candle_poly_var coordinate)
        candle_packed_delta_poly)`;;

let candle_packed_delta_product_source_expr_def = new_definition
 `candle_packed_delta_product_source_expr coordinate =
    Candle_analytic_poly
      (candle_packed_delta_product_source_poly coordinate)`;;

let candle_packed_delta_product_source_value = prove
 (`!environment coordinate.
     candle_analytic_value environment
       (candle_packed_delta_product_source_expr coordinate) =
     candle_analytic_value environment
       (candle_packed_delta_product_expr coordinate)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_packed_delta_product_source_expr_def;
              candle_packed_delta_product_source_poly_def;
              candle_packed_delta_product_expr_def;
              candle_packed_four_expr_def;
              candle_packed_coordinate_expr_def;
              candle_packed_delta_expr_def;
              candle_analytic_value_def; candle_poly_value_list_def;
              candle_q_real_def; candle_q_den_def;
              candle_lc_zreal_def; FST; SND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_DIV_1]);;

let candle_packed_delta_product_source_d = prove
 (`!environment coordinate derivative_coordinate.
     candle_analytic_d derivative_coordinate environment
       (candle_packed_delta_product_source_expr coordinate) =
     candle_analytic_d derivative_coordinate environment
       (candle_packed_delta_product_expr coordinate)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_packed_delta_product_source_expr_def;
              candle_packed_delta_product_source_poly_def;
              candle_packed_delta_product_expr_def;
              candle_packed_four_expr_def;
              candle_packed_coordinate_expr_def;
              candle_packed_delta_expr_def;
              candle_analytic_value_def; candle_analytic_d_def;
              candle_poly_value_list_def; candle_poly_d_list_def;
              candle_q_real_def; candle_q_den_def;
              candle_lc_zreal_def; FST; SND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_DIV_1;
              REAL_MUL_LZERO; REAL_MUL_RZERO;
              REAL_ADD_LID; REAL_ADD_RID]);;

let candle_packed_delta_product_source_dd = prove
 (`!environment coordinate rowindex colindex.
     candle_analytic_dd rowindex colindex environment
       (candle_packed_delta_product_source_expr coordinate) =
     candle_analytic_dd rowindex colindex environment
       (candle_packed_delta_product_expr coordinate)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_packed_delta_product_source_expr_def;
              candle_packed_delta_product_source_poly_def;
              candle_packed_delta_product_expr_def;
              candle_packed_four_expr_def;
              candle_packed_coordinate_expr_def;
              candle_packed_delta_expr_def;
              candle_analytic_value_def; candle_analytic_d_def;
              candle_analytic_dd_def; candle_poly_value_list_def;
              candle_poly_d_list_def; candle_poly_dd_list_def;
              candle_q_real_def; candle_q_den_def;
              candle_lc_zreal_def; FST; SND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_DIV_1;
              REAL_MUL_LZERO; REAL_MUL_RZERO;
              REAL_ADD_LID; REAL_ADD_RID;
              REAL_MUL_AC; REAL_ADD_AC]);;

let candle_q_dim_analytic_contains_delta_product_source = prove
 (`!dimension jet environment coordinate.
     candle_q_dim_analytic_contains dimension jet environment
       (candle_packed_delta_product_source_expr coordinate) <=>
     candle_q_dim_analytic_contains dimension jet environment
       (candle_packed_delta_product_expr coordinate)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_analytic_contains_def;
              candle_packed_delta_product_source_value;
              candle_packed_delta_product_source_d;
              candle_packed_delta_product_source_dd]);;

let candle_q_packed_delta_product_source_result_analytic_invariant = prove
 (`!boxes coordinate.
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     coordinate < 3
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       (ARB:real^6) boxes
       (candle_q_packed_delta_product_result boxes coordinate)
       (candle_packed_delta_product_source_expr coordinate)
       (candle_packed_delta_product_source_expr coordinate)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
    (MATCH_MP
      (SPECL
        [`boxes:((((num#num)#num)#((num#num)#num))list)`;
         `coordinate:num`]
        candle_q_packed_delta_product_result_analytic_invariant)
      (end_itlist CONJ
        [ASSUME
          `LENGTH
            (boxes:((((num#num)#num)#((num#num)#num))list)) = 6`;
         ASSUME
          `candle_q_box_valid_list
            (boxes:((((num#num)#num)#((num#num)#num))list))`;
         ASSUME `(coordinate:num) < 3`])) THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def;
              candle_q_dim_analytic_contains_delta_product_source;
              candle_packed_delta_product_source_expr_def;
              candle_packed_delta_product_source_poly_def;
              candle_packed_delta_product_expr_def;
              candle_packed_four_expr_def;
              candle_packed_coordinate_expr_def;
              candle_packed_delta_expr_def;
              candle_analytic_regular_at_def]);;

let candle_packed_delta_neg_derivative_source_instruction_def =
  new_definition
 `candle_packed_delta_neg_derivative_source_instruction coordinate source <=>
    (coordinate = 3 \/ coordinate = 4 \/ coordinate = 5) /\
    source =
      Candle_analytic_push_poly
        (candle_poly_compile
          (candle_packed_delta_neg_derivative_poly coordinate))`;;

let candle_packed_delta_product_source_instruction_def = new_definition
 `candle_packed_delta_product_source_instruction coordinate source <=>
    coordinate < 3 /\
    source =
      Candle_analytic_push_poly
        (candle_poly_compile
          (candle_packed_delta_product_source_poly coordinate))`;;

let candle_packed_delta_neg_derivative_source_compile = prove
 (`!coordinate source.
     candle_packed_delta_neg_derivative_source_instruction coordinate source
     ==>
     (coordinate = 3 \/ coordinate = 4 \/ coordinate = 5) /\
     candle_analytic_compile
       (candle_packed_delta_neg_derivative_expr coordinate) = [source]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_packed_delta_neg_derivative_source_instruction_def;
              candle_packed_delta_neg_derivative_expr_def;
              candle_analytic_compile_def] THEN
  MESON_TAC[]);;

let candle_packed_delta_product_source_compile = prove
 (`!coordinate source.
     candle_packed_delta_product_source_instruction coordinate source
     ==>
     coordinate < 3 /\
     candle_analytic_compile
       (candle_packed_delta_product_source_expr coordinate) = [source]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_packed_delta_product_source_instruction_def;
              candle_packed_delta_product_source_expr_def;
              candle_analytic_compile_def] THEN
  MESON_TAC[]);;

let candle_q_packed_delta_specialized_source_result_def = new_definition
 `candle_q_packed_delta_specialized_source_result boxes source result expression <=>
    (?coordinate.
       candle_packed_delta_neg_derivative_source_instruction coordinate source /\
       result =
         candle_q_packed_delta_neg_derivative_result boxes coordinate /\
       expression = candle_packed_delta_neg_derivative_expr coordinate) \/
    (?coordinate.
       candle_packed_delta_product_source_instruction coordinate source /\
       result = candle_q_packed_delta_product_result boxes coordinate /\
       expression = candle_packed_delta_product_source_expr coordinate)`;;

let candle_q_packed_delta_specialized_source_result_analytic_invariant = prove
 (`!boxes source result expression.
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     candle_q_packed_delta_specialized_source_result
       boxes source result expression
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       (ARB:real^6) boxes result expression expression`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM MP_TAC THEN
  REWRITE_TAC[candle_q_packed_delta_specialized_source_result_def] THEN
  DISCH_THEN
    (DISJ_CASES_THEN
      (X_CHOOSE_THEN `coordinate:num` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THENL
   [RULE_ASSUM_TAC
      (REWRITE_RULE
        [candle_packed_delta_neg_derivative_source_instruction_def]) THEN
    MATCH_MP_TAC
      candle_q_packed_delta_neg_derivative_result_analytic_invariant THEN
    ASM_REWRITE_TAC[];
    RULE_ASSUM_TAC
      (REWRITE_RULE
        [candle_packed_delta_product_source_instruction_def]) THEN
    MATCH_MP_TAC
      candle_q_packed_delta_product_source_result_analytic_invariant THEN
    ASM_REWRITE_TAC[]]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_packed_delta_product_source_value;
     candle_packed_delta_product_source_d;
     candle_packed_delta_product_source_dd;
     candle_q_dim_analytic_contains_delta_product_source;
     candle_q_packed_delta_product_source_result_analytic_invariant;
     candle_packed_delta_neg_derivative_source_compile;
     candle_packed_delta_product_source_compile;
     candle_q_packed_delta_specialized_source_result_analytic_invariant] then
  failwith "packed delta specialization sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_DELTA_SPECIALIZATION_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
