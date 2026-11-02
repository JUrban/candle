(* ========================================================================== *)
(* Executable exact object-q completion, negation, and addition.             *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  These operations preserve the raw rational   *)
(* arithmetic of the HOL4 object state.  In particular, addition deliberately *)
(* does not insert the normalization used by the older generic jet evaluator. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_algebraic_compute.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_delta_neg_derivative_result_compute.ml";;

module Candle_cv_analytic_expr_packed_source_object_linear_compute = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_analytic_expr_taylor_model_packed_object_compute;;
open Candle_cv_analytic_expr_taylor_model_packed_object_gradient_sound;;
open Candle_cv_analytic_expr_packed_source_delta_neg_derivative_result_compute;;
open Candle_cv_analytic_expr_packed_source_object_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_add_sound;;
open Candle_cv_analytic_expr_packed_source_object_neg_sound;;
open Candle_cv_analytic_expr_packed_source_object_representation;;
open Candle_cv_analytic_expr_packed_source_object_algebraic_compute;;

(* Raw pairwise interval addition.  Well-formed object fields have matching  *)
(* lengths; the numeric cases make malformed cval lists fail to empty.       *)

let candle_cv_q_packed_object_interval_list_add_def = define
 `(candle_cv_q_packed_object_interval_list_add (Cexp_num n) ys =
     Cexp_num 0) /\
  (candle_cv_q_packed_object_interval_list_add
     (Cexp_pair x xs) (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_q_packed_object_interval_list_add
     (Cexp_pair x xs) (Cexp_pair y ys) =
     Cexp_pair (candle_cv_q_interval_add x y)
       (candle_cv_q_packed_object_interval_list_add xs ys))`;;

let candle_cv_q_packed_object_interval_list_add_map2_correct = prove
 (`!xs ys.
     LENGTH xs = LENGTH ys
     ==>
     candle_cv_q_packed_object_interval_list_add
       (candle_cv_q_interval_list xs) (candle_cv_q_interval_list ys) =
     candle_cv_q_interval_list
       (MAP2 candle_q_interval_add xs ys)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ;
              candle_cv_q_interval_list_def;
              candle_cv_q_packed_object_interval_list_add_def;
              MAP2_DEF; HD; TL; candle_cv_q_interval_add_correct] THEN
  DISCH_TAC THEN AP_TERM_TAC THEN ASM_MESON_TAC[]);;

let candle_cv_q_packed_object_interval_list_add_correct = prove
 (`!xs ys.
     LENGTH xs = LENGTH ys
     ==>
     candle_cv_q_packed_object_interval_list_add
       (candle_cv_q_interval_list xs) (candle_cv_q_interval_list ys) =
     candle_cv_q_interval_list
       (candle_q_packed_object_interval_list_add xs ys)`,
  REWRITE_TAC[candle_q_packed_object_interval_list_add_def] THEN
  MESON_TAC[candle_cv_q_packed_object_interval_list_add_map2_correct]);;

let candle_q_packed_object_hessian_add_eq = prove
 (`!left right.
     candle_q_packed_object_hessian_add left right =
     candle_q_packed_object_interval_list_add left right`,
  REWRITE_TAC[candle_q_packed_object_hessian_add_def;
              candle_q_packed_object_interval_list_add_def]);;

let _ = print_endline "CANDLE_OBJECT_LINEAR_STAGE list-add";;

let candle_cv_q_packed_object_gradient_row_complete_def = new_definition
 `candle_cv_q_packed_object_gradient_row_complete
      radii center_entry interval_row =
    let variation = candle_cv_q_dot_abs_upper radii interval_row in
    let error = candle_cv_q_add variation variation in
    let half_error = candle_cv_q_mul error candle_cv_q_half in
    candle_cv_q_interval_add center_entry
      (Cexp_pair (candle_cv_q_neg half_error) half_error)`;;

let candle_cv_q_packed_object_gradient_row_complete_correct = prove
 (`!radii center_entry interval_row.
     candle_cv_q_packed_object_gradient_row_complete
       (candle_cv_q_list radii) (candle_cv_q_interval center_entry)
       (candle_cv_q_interval_list interval_row) =
     candle_cv_q_interval
       (candle_q_packed_object_gradient_row_complete
         radii center_entry interval_row)`,
  REWRITE_TAC[candle_cv_q_packed_object_gradient_row_complete_def;
              candle_q_packed_object_gradient_row_complete_def;
              candle_cv_q_dot_abs_upper_correct;
              candle_cv_q_add_correct; candle_cv_q_mul_correct;
              candle_cv_q_half_def; candle_cv_q_symmetric_interval_correct;
              candle_cv_q_interval_add_correct; LET_DEF; LET_END_DEF]);;

let _ = print_endline "CANDLE_OBJECT_LINEAR_STAGE gradient-row";;

let candle_cv_q_packed_object_gradient_rows_complete_def = define
 `(candle_cv_q_packed_object_gradient_rows_complete
     radii (Cexp_num n) interval_rows = Cexp_num 0) /\
  (candle_cv_q_packed_object_gradient_rows_complete
     radii (Cexp_pair center_entry center_rest) (Cexp_num n) =
     Cexp_num 0) /\
  (candle_cv_q_packed_object_gradient_rows_complete
     radii (Cexp_pair center_entry center_rest)
       (Cexp_pair interval_row interval_rows) =
     Cexp_pair
       (candle_cv_q_packed_object_gradient_row_complete
         radii center_entry interval_row)
       (candle_cv_q_packed_object_gradient_rows_complete
         radii center_rest interval_rows))`;;

let candle_cv_q_packed_object_gradient_rows_complete_correct = prove
 (`!radii center_gradient interval_rows.
     candle_cv_q_packed_object_gradient_rows_complete
       (candle_cv_q_list radii)
       (candle_cv_q_interval_list center_gradient)
       (candle_cv_q_interval_matrix interval_rows) =
     candle_cv_q_interval_list
       (candle_q_packed_object_gradient_rows_complete
         radii center_gradient interval_rows)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_q_interval_list_def;
                candle_cv_q_packed_object_gradient_rows_complete_def;
                candle_q_packed_object_gradient_rows_complete_def];
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[candle_cv_q_interval_list_def;
                    candle_cv_q_interval_matrix_def;
                    candle_cv_q_packed_object_gradient_rows_complete_def;
                    candle_q_packed_object_gradient_rows_complete_def;
                    candle_cv_q_packed_object_gradient_row_complete_correct]]);;

let _ = print_endline "CANDLE_OBJECT_LINEAR_STAGE gradient-rows";;

let candle_cv_q_packed_object_gradient_complete6_def = new_definition
 `candle_cv_q_packed_object_gradient_complete6
      radii center_gradient packed_hessian =
    candle_cv_q_packed_object_gradient_rows_complete radii center_gradient
      (candle_cv_q_packed_hessian6_expand packed_hessian)`;;

let candle_cv_q_packed_object_gradient_complete6_correct = prove
 (`!radii center_gradient packed_hessian.
     LENGTH packed_hessian = 21
     ==>
     candle_cv_q_packed_object_gradient_complete6
       (candle_cv_q_list radii)
       (candle_cv_q_interval_list center_gradient)
       (candle_cv_q_interval_list packed_hessian) =
     candle_cv_q_interval_list
       (candle_q_packed_object_gradient_complete6
         radii center_gradient packed_hessian)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_cv_q_packed_object_gradient_complete6_def;
              candle_q_packed_object_gradient_complete6_def] THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_hessian6_expand
      (candle_cv_q_interval_list packed_hessian) =
    candle_cv_q_interval_matrix
      (candle_q_packed_hessian6_expand packed_hessian)`
   SUBST1_TAC THENL
   [MATCH_MP_TAC candle_cv_q_packed_hessian6_expand_correct THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_cv_q_packed_object_gradient_rows_complete_correct]]);;

let _ = print_endline "CANDLE_OBJECT_LINEAR_STAGE gradient-complete";;

let candle_cv_q_packed_object_state_recomplete_def = new_definition
 `candle_cv_q_packed_object_state_recomplete
      radii domain center_value center_gradient packed_hessian =
    candle_cv_q_packed_object_state_make domain center_value center_gradient
      (candle_cv_q_packed_object_value_bound6
        radii center_value center_gradient packed_hessian)
      (candle_cv_q_packed_object_gradient_complete6
        radii center_gradient packed_hessian)
      packed_hessian`;;

let candle_cv_q_packed_object_state_recomplete_correct = prove
 (`!radii domain center_value center_gradient packed_hessian.
     LENGTH radii = 6 /\ LENGTH packed_hessian = 21
     ==>
     candle_cv_q_packed_object_state_recomplete
       (candle_cv_q_list radii) (candle_cv_bool domain)
       (candle_cv_q_interval center_value)
       (candle_cv_q_interval_list center_gradient)
       (candle_cv_q_interval_list packed_hessian) =
     candle_cv_q_packed_object_state_encode
       (Candle_q_packed_object_state domain center_value center_gradient
         (candle_q_packed_object_value_bound6
           radii center_value center_gradient packed_hessian)
         (candle_q_packed_object_gradient_complete6
           radii center_gradient packed_hessian)
         packed_hessian)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_q_packed_object_value_bound6_lookup
      radii center_value center_gradient packed_hessian =
    candle_q_packed_object_value_bound6
      radii center_value center_gradient packed_hessian`
   ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_packed_object_value_bound6_lookup_eq THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_object_gradient_complete6
      (candle_cv_q_list radii)
      (candle_cv_q_interval_list center_gradient)
      (candle_cv_q_interval_list packed_hessian) =
    candle_cv_q_interval_list
      (candle_q_packed_object_gradient_complete6
        radii center_gradient packed_hessian)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC candle_cv_q_packed_object_gradient_complete6_correct THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[candle_cv_q_packed_object_state_recomplete_def;
              candle_cv_q_packed_object_state_encode_def] THEN
  ASM_REWRITE_TAC[candle_cv_q_packed_object_value_bound6_correct]);;

let _ = print_endline "CANDLE_OBJECT_LINEAR_STAGE state-recomplete";;

let candle_cv_q_packed_object_state_neg_def = new_definition
 `candle_cv_q_packed_object_state_neg radii state =
    let center_value = candle_cv_q_interval_neg
      (candle_cv_q_packed_object_state_center_value state) in
    let center_gradient = candle_cv_q_dim_interval_list_neg
      (candle_cv_q_packed_object_state_center_gradient state) in
    let packed_hessian = candle_cv_q_dim_interval_list_neg
      (candle_cv_q_packed_object_state_packed_hessian state) in
    candle_cv_q_packed_object_state_recomplete radii
      (candle_cv_q_packed_object_state_domain state)
      center_value center_gradient packed_hessian`;;

let candle_cv_q_packed_object_state_neg_correct = prove
 (`!radii domain center_value center_gradient value_bound gradient_bounds
       packed_hessian.
     LENGTH radii = 6 /\ LENGTH packed_hessian = 21
     ==>
     candle_cv_q_packed_object_state_neg (candle_cv_q_list radii)
       (candle_cv_q_packed_object_state_encode
         (Candle_q_packed_object_state domain center_value center_gradient
           value_bound gradient_bounds packed_hessian)) =
     candle_cv_q_packed_object_state_encode
       (Candle_q_packed_object_state domain
         (candle_q_interval_neg center_value)
         (candle_q_dim_interval_list_neg center_gradient)
         (candle_q_packed_object_value_bound6 radii
           (candle_q_interval_neg center_value)
           (candle_q_dim_interval_list_neg center_gradient)
           (candle_q_packed_object_hessian_neg packed_hessian))
         (candle_q_packed_object_gradient_complete6 radii
           (candle_q_dim_interval_list_neg center_gradient)
           (candle_q_packed_object_hessian_neg packed_hessian))
         (candle_q_packed_object_hessian_neg packed_hessian))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_cv_q_packed_object_state_neg_def; LET_DEF; LET_END_DEF;
              candle_cv_q_packed_object_state_domain_correct;
              candle_cv_q_packed_object_state_center_value_correct;
              candle_cv_q_packed_object_state_center_gradient_correct;
              candle_cv_q_packed_object_state_packed_hessian_correct;
              candle_cv_q_interval_neg_correct;
              candle_cv_q_dim_interval_list_neg_correct;
              candle_q_dim_interval_list_neg_map;
              candle_q_packed_object_hessian_neg_def] THEN
  MATCH_MP_TAC candle_cv_q_packed_object_state_recomplete_correct THEN
  ASM_REWRITE_TAC[LENGTH_MAP]);;

let _ = print_endline "CANDLE_OBJECT_LINEAR_STAGE state-neg";;

let candle_cv_q_packed_object_state_add_def = new_definition
 `candle_cv_q_packed_object_state_add radii left right =
    let center_value = candle_cv_q_interval_add
      (candle_cv_q_packed_object_state_center_value left)
      (candle_cv_q_packed_object_state_center_value right) in
    let center_gradient = candle_cv_q_packed_object_interval_list_add
      (candle_cv_q_packed_object_state_center_gradient left)
      (candle_cv_q_packed_object_state_center_gradient right) in
    let packed_hessian = candle_cv_q_packed_object_interval_list_add
      (candle_cv_q_packed_object_state_packed_hessian left)
      (candle_cv_q_packed_object_state_packed_hessian right) in
    candle_cv_q_packed_object_state_recomplete radii
      (candle_cv_bool_and
        (candle_cv_q_packed_object_state_domain left)
        (candle_cv_q_packed_object_state_domain right))
      center_value center_gradient packed_hessian`;;

let candle_cv_q_packed_object_state_add_correct = prove
 (`!radii left_domain left_center_value left_center_gradient
       left_value_bound left_gradient_bounds left_hessian
       right_domain right_center_value right_center_gradient
       right_value_bound right_gradient_bounds right_hessian.
     LENGTH radii = 6 /\
     LENGTH left_center_gradient = 6 /\
     LENGTH right_center_gradient = 6 /\
     LENGTH left_hessian = 21 /\ LENGTH right_hessian = 21
     ==>
     candle_cv_q_packed_object_state_add (candle_cv_q_list radii)
       (candle_cv_q_packed_object_state_encode
         (Candle_q_packed_object_state left_domain left_center_value
           left_center_gradient left_value_bound left_gradient_bounds
           left_hessian))
       (candle_cv_q_packed_object_state_encode
         (Candle_q_packed_object_state right_domain right_center_value
           right_center_gradient right_value_bound right_gradient_bounds
           right_hessian)) =
     candle_cv_q_packed_object_state_encode
       (Candle_q_packed_object_state (left_domain /\ right_domain)
         (candle_q_interval_add left_center_value right_center_value)
         (candle_q_packed_object_interval_list_add
           left_center_gradient right_center_gradient)
         (candle_q_packed_object_value_bound6 radii
           (candle_q_interval_add left_center_value right_center_value)
           (candle_q_packed_object_interval_list_add
             left_center_gradient right_center_gradient)
           (candle_q_packed_object_hessian_add
             left_hessian right_hessian))
         (candle_q_packed_object_gradient_complete6 radii
           (candle_q_packed_object_interval_list_add
             left_center_gradient right_center_gradient)
           (candle_q_packed_object_hessian_add
             left_hessian right_hessian))
         (candle_q_packed_object_hessian_add left_hessian right_hessian))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_object_interval_list_add
      (candle_cv_q_interval_list left_center_gradient)
      (candle_cv_q_interval_list right_center_gradient) =
    candle_cv_q_interval_list
      (candle_q_packed_object_interval_list_add
        left_center_gradient right_center_gradient)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC candle_cv_q_packed_object_interval_list_add_correct THEN
    TRANS_TAC EQ_TRANS `6` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_object_interval_list_add
      (candle_cv_q_interval_list left_hessian)
      (candle_cv_q_interval_list right_hessian) =
    candle_cv_q_interval_list
      (candle_q_packed_object_interval_list_add
        left_hessian right_hessian)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC candle_cv_q_packed_object_interval_list_add_correct THEN
    TRANS_TAC EQ_TRANS `21` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  let hessian_lengths_equal =
    TRANS
      (ASSUME
        `LENGTH
          (left_hessian:
            ((((num#num)#num)#((num#num)#num))list)) = 21`)
      (SYM
        (ASSUME
          `LENGTH
            (right_hessian:
              ((((num#num)#num)#((num#num)#num))list)) = 21`)) in
  let added_hessian_length =
    MATCH_MP
      (SPECL
        [`left_hessian:
            ((((num#num)#num)#((num#num)#num))list)`;
         `right_hessian:
            ((((num#num)#num)#((num#num)#num))list)`]
        candle_q_packed_object_interval_list_add_length)
      hessian_lengths_equal in
  ASM_REWRITE_TAC
    [candle_cv_q_packed_object_state_add_def; LET_DEF; LET_END_DEF;
     candle_cv_q_packed_object_state_domain_correct;
     candle_cv_q_packed_object_state_center_value_correct;
     candle_cv_q_packed_object_state_center_gradient_correct;
     candle_cv_q_packed_object_state_packed_hessian_correct;
     candle_cv_q_interval_add_correct;
     candle_cv_bool_and_correct;
     candle_q_packed_object_hessian_add_eq] THEN
  MATCH_MP_TAC candle_cv_q_packed_object_state_recomplete_correct THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MP_TAC added_hessian_length THEN ASM_REWRITE_TAC[]]);;

let _ = print_endline "CANDLE_OBJECT_LINEAR_STAGE state-add";;

if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_q_packed_object_interval_list_add_map2_correct;
     candle_cv_q_packed_object_interval_list_add_correct;
     candle_q_packed_object_hessian_add_eq;
     candle_cv_q_packed_object_gradient_row_complete_correct;
     candle_cv_q_packed_object_gradient_rows_complete_correct;
     candle_cv_q_packed_object_gradient_complete6_correct;
     candle_cv_q_packed_object_state_recomplete_correct;
     candle_cv_q_packed_object_state_neg_correct;
     candle_cv_q_packed_object_state_add_correct] then
  failwith "packed object linear compute: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_LINEAR_COMPUTE_OK DEVELOPMENT_NON_RELEASE";;

end;;
