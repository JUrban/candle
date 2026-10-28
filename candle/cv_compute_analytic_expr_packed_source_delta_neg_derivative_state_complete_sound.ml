(* ========================================================================== *)
(* Complete state soundness for the optimized negative delta derivatives.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The center value and gradient are proved in  *)
(* the predecessor.  This child proves that the exact object construction   *)
(* used by the fast checker also encloses the complete packed Hessian of     *)
(* [--(partial delta / partial x_i)] throughout every box.  Since delta is  *)
(* cubic, this Hessian is the constant negated delta Hessian evaluated on    *)
(* the selected coordinate unit vector.                                     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_delta_neg_derivative_state_sound.ml";;

module Candle_cv_analytic_expr_packed_source_delta_neg_derivative_state_complete_sound = struct

open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_jet;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_packed_source_delta_hessian;;
open Candle_cv_analytic_expr_packed_source_delta_analytic;;
open Candle_cv_analytic_expr_packed_source_delta_neg_derivative_analytic;;
open Candle_cv_analytic_expr_packed_source_delta_neg_derivative_state_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_hessian_sound;;

let candle_q_packed_delta_basis_six_def = new_definition
 `candle_q_packed_delta_basis_six coordinate =
    [if coordinate = 0 then candle_q_one_interval else candle_q_zero_interval;
     if coordinate = 1 then candle_q_one_interval else candle_q_zero_interval;
     if coordinate = 2 then candle_q_one_interval else candle_q_zero_interval;
     if coordinate = 3 then candle_q_one_interval else candle_q_zero_interval;
     if coordinate = 4 then candle_q_one_interval else candle_q_zero_interval;
     if coordinate = 5 then candle_q_one_interval else candle_q_zero_interval]`;;

let candle_q_packed_delta_neg_derivative_hessian_six_def = new_definition
 `candle_q_packed_delta_neg_derivative_hessian_six coordinate =
    let basis = candle_q_packed_delta_basis_six coordinate in
    candle_q_dim_interval_list_neg
      (candle_q_packed_delta_hessian_six
        (EL 0 basis) (EL 1 basis) (EL 2 basis)
        (EL 3 basis) (EL 4 basis) (EL 5 basis))`;;

let candle_q_packed_delta_basis_six_contains = prove
 (`!coordinate basis_index.
     basis_index < 6
     ==> candle_q_interval_contains
           (EL basis_index (candle_q_packed_delta_basis_six coordinate))
           (EL basis_index (candle_real_packed_delta_basis_six coordinate))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC
   (ARITH_RULE
     `basis_index < 6
      ==> basis_index = 0 \/ basis_index = 1 \/ basis_index = 2 \/
          basis_index = 3 \/ basis_index = 4 \/ basis_index = 5`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[candle_q_packed_delta_basis_six_def;
              candle_real_packed_delta_basis_six_def] THEN
  CONV_TAC (DEPTH_CONV EL_CONV) THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[candle_q_one_interval_contains;
                  candle_q_zero_interval_contains]);;

let candle_q_packed_delta_basis_hessian_contains = prove
 (`!coordinate.
     candle_q_stack_contains
       (candle_q_packed_delta_hessian_six
         (EL 0 (candle_q_packed_delta_basis_six coordinate))
         (EL 1 (candle_q_packed_delta_basis_six coordinate))
         (EL 2 (candle_q_packed_delta_basis_six coordinate))
         (EL 3 (candle_q_packed_delta_basis_six coordinate))
         (EL 4 (candle_q_packed_delta_basis_six coordinate))
         (EL 5 (candle_q_packed_delta_basis_six coordinate)))
       (candle_real_packed_delta_hessian_six
         (EL 0 (candle_real_packed_delta_basis_six coordinate))
         (EL 1 (candle_real_packed_delta_basis_six coordinate))
         (EL 2 (candle_real_packed_delta_basis_six coordinate))
         (EL 3 (candle_real_packed_delta_basis_six coordinate))
         (EL 4 (candle_real_packed_delta_basis_six coordinate))
         (EL 5 (candle_real_packed_delta_basis_six coordinate)))`,
  GEN_TAC THEN REWRITE_TAC[candle_q_stack_contains_all2] THEN
  MATCH_MP_TAC candle_q_packed_delta_hessian_six_sound THEN
  REPEAT CONJ_TAC THEN
  MATCH_MP_TAC candle_q_packed_delta_basis_six_contains THEN
  ARITH_TAC);;

let candle_real_packed_delta_neg_derivative_hessian_six_length = prove
 (`!coordinate.
     LENGTH (candle_real_packed_delta_neg_derivative_hessian_six coordinate) =
     21`,
  GEN_TAC THEN
  REWRITE_TAC[candle_real_packed_delta_neg_derivative_hessian_six_def;
              LENGTH_MAP; candle_real_packed_delta_hessian_six_def;
              candle_real_packed_delta_hessian_rows_six_def;
              candle_real_packed_delta_sums_def; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_list_eq_list_of_seq_el_21 = prove
 (`!items:A list.
     LENGTH items = 21
     ==> items = list_of_seq (\lookup_index. EL lookup_index items) 21`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `lookup_index:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ]);;

let candle_packed_delta_neg_derivative_analytic_hessian_six = prove
 (`!v0 v1 v2 v3 v4 v5 coordinate.
     (coordinate = 3 \/ coordinate = 4 \/ coordinate = 5)
     ==>
     candle_q_packed_hessian6_values
       (\rowindex colindex.
         candle_analytic_dd rowindex colindex
           [v0;v1;v2;v3;v4;v5]
           (candle_packed_delta_neg_derivative_expr coordinate)) =
     candle_real_packed_delta_neg_derivative_hessian_six coordinate`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  let reconstruction =
    MATCH_MP
      (ISPEC
        `candle_real_packed_delta_neg_derivative_hessian_six coordinate`
        candle_list_eq_list_of_seq_el_21)
      (SPEC `coordinate:num`
        candle_real_packed_delta_neg_derivative_hessian_six_length) in
  let coordinate_cases =
    ASSUME `coordinate = 3 \/ coordinate = 4 \/ coordinate = 5` in
  let component rowindex colindex =
    let bounds =
      prove
       (vsubst
         [rowindex,`rowindex:num`; colindex,`colindex:num`]
         `rowindex < 6 /\ rowindex <= colindex /\ colindex < 6`,
        CONV_TAC NUM_REDUCE_CONV) in
    MATCH_MP
      (SPECL
        [`v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;`v5:real`;
         `coordinate:num`; rowindex; colindex]
        candle_packed_delta_neg_derivative_analytic_dd_upper)
      (CONJ coordinate_cases bounds) in
  let components =
    map
      (fun (rowindex,colindex) ->
        component (mk_small_numeral rowindex) (mk_small_numeral colindex))
      [(0,0);(0,1);(0,2);(0,3);(0,4);(0,5);
       (1,1);(1,2);(1,3);(1,4);(1,5);
       (2,2);(2,3);(2,4);(2,5);
       (3,3);(3,4);(3,5);(4,4);(4,5);(5,5)] in
  ONCE_REWRITE_TAC[reconstruction] THEN
  REWRITE_TAC[candle_q_packed_hessian6_values_def] THEN
  EVERY (map (fun theorem -> ONCE_REWRITE_TAC[theorem]) components) THEN
  REWRITE_TAC
   [candle_packed_delta_hessian_upper_index_def;
     num_CONV `21`; num_CONV `20`; num_CONV `19`;
     num_CONV `18`; num_CONV `17`; num_CONV `16`;
     num_CONV `15`; num_CONV `14`; num_CONV `13`;
     num_CONV `12`; num_CONV `11`; num_CONV `10`;
     num_CONV `9`; num_CONV `8`; num_CONV `7`; num_CONV `6`;
     num_CONV `5`; num_CONV `4`; num_CONV `3`; num_CONV `2`;
     num_CONV `1`; list_of_seq; APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_q_packed_delta_neg_derivative_hessian_six_sound = prove
 (`!v0 v1 v2 v3 v4 v5 coordinate.
     (coordinate = 3 \/ coordinate = 4 \/ coordinate = 5)
     ==>
     candle_q_stack_contains
       (candle_q_packed_delta_neg_derivative_hessian_six coordinate)
       (candle_q_packed_hessian6_values
         (\rowindex colindex.
           candle_analytic_dd rowindex colindex
             [v0;v1;v2;v3;v4;v5]
             (candle_packed_delta_neg_derivative_expr coordinate)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  let basis_contains =
    SPEC `coordinate:num` candle_q_packed_delta_basis_hessian_contains in
  let negated_contains =
    MATCH_MP candle_q_dim_interval_list_neg_contains basis_contains in
  let table_contains =
    REWRITE_RULE
      [GSYM candle_q_packed_delta_neg_derivative_hessian_six_def;
       GSYM candle_real_packed_delta_neg_derivative_hessian_six_def;
       LET_DEF; LET_END_DEF]
      negated_contains in
  let analytic_table =
    MATCH_MP
      (SPECL
        [`v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;`v5:real`;
         `coordinate:num`]
        candle_packed_delta_neg_derivative_analytic_hessian_six)
      (ASSUME `coordinate = 3 \/ coordinate = 4 \/ coordinate = 5`) in
  ONCE_REWRITE_TAC[analytic_table] THEN
  REWRITE_TAC[candle_q_packed_delta_neg_derivative_hessian_six_def;
              LET_DEF; LET_END_DEF] THEN
  ACCEPT_TAC table_contains);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_delta_basis_six_contains;
     candle_q_packed_delta_basis_hessian_contains;
     candle_real_packed_delta_neg_derivative_hessian_six_length;
     candle_list_eq_list_of_seq_el_21;
     candle_packed_delta_neg_derivative_analytic_hessian_six;
     candle_q_packed_delta_neg_derivative_hessian_six_sound] then
  failwith "packed source negative delta derivative complete state: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_DELTA_NEG_DERIVATIVE_STATE_COMPLETE_OK DEVELOPMENT_NON_RELEASE";;

end;;
