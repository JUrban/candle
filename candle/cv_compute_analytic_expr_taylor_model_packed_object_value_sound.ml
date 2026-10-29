(* ========================================================================== *)
(* Full interval soundness for exact packed-object Taylor value completion.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The established packed-object theorem        *)
(* identifies the completed upper endpoint used by the fast negativity      *)
(* check.  The object analytic invariant also needs the lower endpoint.      *)
(* This file proves that endpoint and lifts the existing exact Taylor        *)
(* containment theorem to the faithful packed-object interval.               *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_packed_object_error_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_packed_object_value_sound = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_analytic_expr_extended_taylor;;
open Candle_cv_analytic_expr_taylor_model_program_compute;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_semantics;;
open Candle_cv_analytic_expr_taylor_model_exact_value_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_hessian_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_value_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_object_error_sound;;

let candle_q_packed_object_value_bound6_lower_real = prove
 (`!radii center_value center_gradient packed.
     LENGTH radii = 6
     ==>
     candle_q_real
       (FST
         (candle_q_packed_object_value_bound6
           radii center_value center_gradient packed)) =
     candle_q_real
       (FST
         (candle_q_dim_taylor_model_value_bound radii
           (candle_q_dim_jet_make center_value center_gradient
             (candle_q_packed_hessian6_expand packed))
           (candle_q_packed_hessian6_expand packed)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC (ISPEC `radii:((num#num)#num)list` candle_q_length_six) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN
   (X_CHOOSE_THEN `r0:(num#num)#num`
    (X_CHOOSE_THEN `r1:(num#num)#num`
     (X_CHOOSE_THEN `r2:(num#num)#num`
      (X_CHOOSE_THEN `r3:(num#num)#num`
       (X_CHOOSE_THEN `r4:(num#num)#num`
        (X_CHOOSE_THEN `r5:(num#num)#num` SUBST_ALL_TAC)))))) THEN
  REWRITE_TAC
   [num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`;
    num_CONV `2`; num_CONV `1`; list_of_seq; APPEND;
    candle_q_packed_object_value_bound6_def;
    candle_q_packed_object_error6_def;
    candle_q_packed_quadratic_abs_upper6_def;
    candle_q_packed_quadratic_terms6_def;
    candle_q_packed_quadratic_term_def;
    candle_q_packed_sum_def;
    candle_q_dim_taylor_model_value_bound_real;
    candle_q_dim_taylor_model_error_real;
    candle_q_dim_jet_make_def; candle_q_dim_jet_f_def;
    candle_q_dim_jet_gradient_def;
    candle_q_packed_hessian6_expand_def;
    candle_q_weighted_rows_abs_upper_extended_real;
    candle_q_dot_abs_upper_extended_real;
    candle_q_weighted_rows_abs_upper_def;
    candle_q_dot_abs_upper_def;
    candle_q_interval_add_def;
    candle_q_real_add; candle_q_real_mul; candle_q_real_neg;
    candle_q_real_half; candle_q_packed_real_zero;
    EL; HD; TL; FST; SND; LET_DEF; LET_END_DEF;
    COND_CLAUSES] THEN
  CONV_TAC (DEPTH_CONV EL_CONV) THEN
  CONV_TAC REAL_FIELD);;

let candle_q_packed_object_value_bound6_contains = prove
 (`!radii center_value center_gradient packed x.
     LENGTH radii = 6 /\
     candle_q_interval_contains
       (candle_q_dim_taylor_model_value_bound radii
         (candle_q_dim_jet_make center_value center_gradient
           (candle_q_packed_hessian6_expand packed))
         (candle_q_packed_hessian6_expand packed)) x
     ==>
     candle_q_interval_contains
       (candle_q_packed_object_value_bound6
         radii center_value center_gradient packed) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_q_interval_contains_def]) THEN
  MP_TAC
    (SPECL
      [`radii:((num#num)#num)list`;
       `center_value:((num#num)#num)#((num#num)#num)`;
       `center_gradient:
          (((num#num)#num)#((num#num)#num))list`;
       `packed:(((num#num)#num)#((num#num)#num))list`]
      candle_q_packed_object_value_bound6_lower_real) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC
    (SPECL
      [`radii:((num#num)#num)list`;
       `center_value:((num#num)#num)#((num#num)#num)`;
       `center_gradient:
          (((num#num)#num)#((num#num)#num))list`;
       `packed:(((num#num)#num)#((num#num)#num))list`]
      candle_q_packed_object_value_bound6_upper_real) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[candle_q_interval_contains_def] THEN
  ASM_REAL_ARITH_TAC);;

let candle_q_packed_object_value_bound6_flyspeck_contains = prove
 (`!(f:real^6->real) (lower:real^6) (upper:real^6) (y:real^6)
       radii center_value center_gradient packed (p:real^6).
     LENGTH radii = 6 /\
     ALL (\r. &0 <= candle_q_real r) radii /\
     m_cell_domain (lower,upper) y (candle_q_list_real_vector radii) /\
     diff2_domain (lower,upper) f /\
     candle_q_interval_contains center_value (f y) /\
     candle_q_stack_contains center_gradient
       (list_of_seq (\di. partial (di + 1) f y) 6) /\
     (!(z:real^6). z IN interval [lower,upper]
       ==> ALL2 candle_q_stack_contains
             (candle_q_packed_hessian6_expand packed)
             (list_of_seq
               (\di. list_of_seq
                 (\dj. partial2 (dj + 1) (di + 1) f z) 6) 6)) /\
     p IN interval [lower,upper]
     ==>
     candle_q_interval_contains
       (candle_q_packed_object_value_bound6
         radii center_value center_gradient packed)
       (f p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_q_packed_object_value_bound6_contains THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC
    (CONV_RULE (DEPTH_CONV DIMINDEX_CONV)
      (INST_TYPE [`:6`,`:N`]
        candle_q_exact_taylor_value_bound_contains)) THEN
  MAP_EVERY EXISTS_TAC
    [`lower:real^6`; `upper:real^6`; `y:real^6`] THEN
  ASM_REWRITE_TAC[]);;

let candle_q_packed_object_value_bound6_analytic_contains = prove
 (`!e (lower:real^6) (upper:real^6) (y:real^6)
       radii center_value center_gradient packed (p:real^6).
     candle_analytic_valid_dim 6 e /\
     (!(z:real^6). z IN interval [lower,upper]
       ==> candle_analytic_regular_at
             (list_of_seq (\k. z$(k + 1)) 6) e) /\
     LENGTH radii = 6 /\
     ALL (\r. &0 <= candle_q_real r) radii /\
     m_cell_domain (lower,upper) y (candle_q_list_real_vector radii) /\
     diff2_domain (lower,upper) (candle_analytic_denote_dim e) /\
     candle_q_interval_contains center_value
       (candle_analytic_denote_dim e y) /\
     candle_q_stack_contains center_gradient
       (list_of_seq
         (\di. partial (di + 1) (candle_analytic_denote_dim e) y) 6) /\
     (!(z:real^6). z IN interval [lower,upper]
       ==> candle_q_stack_contains packed
             (candle_q_packed_hessian6_values
               (\i j. candle_analytic_dd i j
                 (list_of_seq (\k. z$(k + 1)) 6) e))) /\
     p IN interval [lower,upper]
     ==>
     candle_q_interval_contains
       (candle_q_packed_object_value_bound6
         radii center_value center_gradient packed)
       (candle_analytic_denote_dim e p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_q_packed_object_value_bound6_contains THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC candle_q_packed_hessian6_exact_value_bound_contains THEN
  MAP_EVERY EXISTS_TAC
    [`lower:real^6`; `upper:real^6`; `y:real^6`] THEN
  ASM_REWRITE_TAC[]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_object_value_bound6_lower_real;
     candle_q_packed_object_value_bound6_contains;
     candle_q_packed_object_value_bound6_flyspeck_contains;
     candle_q_packed_object_value_bound6_analytic_contains] then
  failwith "packed object value soundness: assumptions";;

print_endline
  "CANDLE_CV_PACKED_OBJECT_VALUE_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
