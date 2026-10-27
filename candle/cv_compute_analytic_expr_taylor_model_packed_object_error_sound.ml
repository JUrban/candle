(* ========================================================================== *)
(* Exact packed Taylor completion agrees with the full 6-by-6 Taylor error. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The fixed-width checker accumulates twice the *)
(* linear error plus the packed upper-triangular quadratic error and applies *)
(* one final factor of one half.  The analytic theorem instead writes the    *)
(* conventional linear + one-half-quadratic formula over a full symmetric   *)
(* matrix.  This file proves that the two exact-rational upper endpoints have *)
(* the same real denotation.                                                  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_packed_value_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_packed_object_error_sound = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_analytic_expr_extended_taylor;;
open Candle_cv_analytic_expr_taylor_model_program_compute;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_semantics;;
open Candle_cv_analytic_expr_taylor_model_packed_hessian_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_value_sound;;

let candle_q_packed_sum_def = define
 `(candle_q_packed_sum [] = candle_q_zero) /\
  (candle_q_packed_sum (CONS h t) =
     candle_q_add h (candle_q_packed_sum t))`;;

let candle_q_packed_quadratic_term_def = new_definition
 `candle_q_packed_quadratic_term left_radius right_radius twice entry =
    let raw =
      candle_q_mul (candle_q_mul left_radius right_radius)
        (candle_q_abs_upper entry) in
    if twice then candle_q_add raw raw else raw`;;

let candle_q_packed_quadratic_terms6_def = new_definition
 `candle_q_packed_quadratic_terms6 radii packed =
    [candle_q_packed_quadratic_term (EL 0 radii) (EL 0 radii) F
       (EL 0 packed);
     candle_q_packed_quadratic_term (EL 0 radii) (EL 1 radii) T
       (EL 1 packed);
     candle_q_packed_quadratic_term (EL 0 radii) (EL 2 radii) T
       (EL 2 packed);
     candle_q_packed_quadratic_term (EL 0 radii) (EL 3 radii) T
       (EL 3 packed);
     candle_q_packed_quadratic_term (EL 0 radii) (EL 4 radii) T
       (EL 4 packed);
     candle_q_packed_quadratic_term (EL 0 radii) (EL 5 radii) T
       (EL 5 packed);
     candle_q_packed_quadratic_term (EL 1 radii) (EL 1 radii) F
       (EL 6 packed);
     candle_q_packed_quadratic_term (EL 1 radii) (EL 2 radii) T
       (EL 7 packed);
     candle_q_packed_quadratic_term (EL 1 radii) (EL 3 radii) T
       (EL 8 packed);
     candle_q_packed_quadratic_term (EL 1 radii) (EL 4 radii) T
       (EL 9 packed);
     candle_q_packed_quadratic_term (EL 1 radii) (EL 5 radii) T
       (EL 10 packed);
     candle_q_packed_quadratic_term (EL 2 radii) (EL 2 radii) F
       (EL 11 packed);
     candle_q_packed_quadratic_term (EL 2 radii) (EL 3 radii) T
       (EL 12 packed);
     candle_q_packed_quadratic_term (EL 2 radii) (EL 4 radii) T
       (EL 13 packed);
     candle_q_packed_quadratic_term (EL 2 radii) (EL 5 radii) T
       (EL 14 packed);
     candle_q_packed_quadratic_term (EL 3 radii) (EL 3 radii) F
       (EL 15 packed);
     candle_q_packed_quadratic_term (EL 3 radii) (EL 4 radii) T
       (EL 16 packed);
     candle_q_packed_quadratic_term (EL 3 radii) (EL 5 radii) T
       (EL 17 packed);
     candle_q_packed_quadratic_term (EL 4 radii) (EL 4 radii) F
       (EL 18 packed);
     candle_q_packed_quadratic_term (EL 4 radii) (EL 5 radii) T
       (EL 19 packed);
     candle_q_packed_quadratic_term (EL 5 radii) (EL 5 radii) F
       (EL 20 packed)]`;;

let candle_q_packed_quadratic_abs_upper6_def = new_definition
 `candle_q_packed_quadratic_abs_upper6 radii packed =
    candle_q_packed_sum
      (candle_q_packed_quadratic_terms6 radii packed)`;;

let candle_q_packed_object_error6_def = new_definition
 `candle_q_packed_object_error6 radii center_gradient packed =
    let linear = candle_q_dot_abs_upper radii center_gradient in
    let quadratic = candle_q_packed_quadratic_abs_upper6 radii packed in
    candle_q_add (candle_q_add linear linear) quadratic`;;

let candle_q_packed_object_value_bound6_def = new_definition
 `candle_q_packed_object_value_bound6
      radii center_value center_gradient packed =
    let half_error =
      candle_q_mul candle_q_half
        (candle_q_packed_object_error6 radii center_gradient packed) in
    candle_q_interval_add center_value
      (candle_q_neg half_error,half_error)`;;

let candle_q_packed_real_zero = prove
 (`candle_q_real candle_q_zero = &0`,
  REWRITE_TAC[candle_q_zero_def; candle_q_real_def; candle_q_den_def;
              candle_lc_zreal_def; FST; SND] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let candle_q_length_six = prove
 (`!items:A list.
     LENGTH items = 6
     ==> ?a b c d e f. items = [a;b;c;d;e;f]`,
  REWRITE_TAC[num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`;
              num_CONV `2`; num_CONV `1`;
              LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  MESON_TAC[]);;

let candle_q_packed_object_value_bound6_upper_real = prove
 (`!radii center_value center_gradient packed.
     LENGTH radii = 6
     ==>
     candle_q_real
       (SND
         (candle_q_packed_object_value_bound6
           radii center_value center_gradient packed)) =
     candle_q_real
       (SND
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

let candle_q_packed_object_value_bound6_negative = prove
 (`!radii center_value center_gradient packed.
     LENGTH radii = 6 /\
     candle_q_real
       (SND
         (candle_q_packed_object_value_bound6
           radii center_value center_gradient packed)) < &0
     ==>
     candle_q_real
       (SND
         (candle_q_dim_taylor_model_value_bound radii
           (candle_q_dim_jet_make center_value center_gradient
             (candle_q_packed_hessian6_expand packed))
           (candle_q_packed_hessian6_expand packed))) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
   (SPECL
     [`radii:((num#num)#num)list`;
      `center_value:((num#num)#num)#((num#num)#num)`;
      `center_gradient:
         (((num#num)#num)#((num#num)#num))list`;
      `packed:(((num#num)#num)#((num#num)#num))list`]
     candle_q_packed_object_value_bound6_upper_real) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let candle_q_packed_object_value_bound6_cell_negative = prove
 (`!e (lower:real^6) (upper:real^6) (y:real^6)
       radii center_value center_gradient packed.
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
     candle_q_real
       (SND
         (candle_q_packed_object_value_bound6
           radii center_value center_gradient packed)) < &0
     ==>
     !(p:real^6). p IN interval [lower,upper]
       ==> candle_analytic_denote_dim e p < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_q_real
      (SND
        (candle_q_dim_taylor_model_value_bound radii
          (candle_q_dim_jet_make center_value center_gradient
            (candle_q_packed_hessian6_expand packed))
          (candle_q_packed_hessian6_expand packed))) < &0`
  ASSUME_TAC THENL
   [MP_TAC
     (SPECL
       [`radii:((num#num)#num)list`;
        `center_value:((num#num)#num)#((num#num)#num)`;
        `center_gradient:
           (((num#num)#num)#((num#num)#num))list`;
        `packed:(((num#num)#num)#((num#num)#num))list`]
       candle_q_packed_object_value_bound6_negative) THEN
    ASM_REWRITE_TAC[];
    MP_TAC
     (ISPECL
       [`e:candle_analytic_expr`;
        `lower:real^6`; `upper:real^6`; `y:real^6`;
        `radii:((num#num)#num)list`;
        `center_value:((num#num)#num)#((num#num)#num)`;
        `center_gradient:
           (((num#num)#num)#((num#num)#num))list`;
        `packed:(((num#num)#num)#((num#num)#num))list`]
       candle_q_packed_hessian6_exact_cell_negative) THEN
    ASM_REWRITE_TAC[]]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_real_zero;
     candle_q_length_six;
     candle_q_packed_object_value_bound6_upper_real;
     candle_q_packed_object_value_bound6_negative;
     candle_q_packed_object_value_bound6_cell_negative] then
  failwith "packed object error soundness: assumptions";;

print_endline
  "CANDLE_CV_PACKED_OBJECT_ERROR_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
