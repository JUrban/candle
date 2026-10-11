(* ========================================================================== *)
(* Soundness bridge from the historical delta jet to its supplied root.      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_delta_root_sound = struct

open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_fixed_scale_angle_polynomials_sound;;

(* [EL] is intentionally total in HOL, but its out-of-range value is not a
   useful analytic contract.  Extend the checked 6-by-6 delta Hessian by zero
   instead.  This gives later chain rules a genuinely total symmetric
   component function while preserving every in-range entry. *)

let candle_fs_hist_delta_hessian_component_real_def = new_definition
 `candle_fs_hist_delta_hessian_component_real
      (values:num->real) i j =
    if i < 6 /\ j < 6 then
      EL j (EL i (candle_fs_hist_delta_hessian_real values))
    else &0`;;

let candle_fs_hist_delta_hessian_real_symmetric = prove
 (`!values i j.
     i < 6 /\ j < 6
     ==> EL j (EL i (candle_fs_hist_delta_hessian_real values)) =
         EL i (EL j (candle_fs_hist_delta_hessian_real values))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (SUBGOAL_THEN
    `i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5`
   MP_TAC THENL
    [ASM_ARITH_TAC;
     DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)]) THEN
  (SUBGOAL_THEN
    `j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5`
   MP_TAC THENL
    [ASM_ARITH_TAC;
     DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)]) THEN
  REWRITE_TAC[candle_fs_hist_delta_hessian_real_def;
              LET_DEF; LET_END_DEF] THEN
  CONV_TAC (DEPTH_CONV EL_CONV) THEN
  REFL_TAC);;

let candle_fs_hist_delta_hessian_component_real_symmetric = prove
 (`!values i j.
     candle_fs_hist_delta_hessian_component_real values i j =
     candle_fs_hist_delta_hessian_component_real values j i`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_delta_hessian_component_real_def;
              CONJ_SYM] THEN
  ASM_CASES_TAC `i < 6 /\ j < 6` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC candle_fs_hist_delta_hessian_real_symmetric THEN
  ASM_REWRITE_TAC[]);;

let candle_fs_hist_delta_hessian_component_real_list_of_seq = prove
  (`!values.
     candle_fs_hist_delta_hessian_real values =
     list_of_seq
       (\i. list_of_seq
         (\j. candle_fs_hist_delta_hessian_component_real values i j)
         6) 6`,
  GEN_TAC THEN
  MP_TAC
    (SPECL
      [`6`; `candle_fs_hist_delta_hessian_real (values:num->real)`]
      candle_fs_hist_matrix_list_of_seq) THEN
  REWRITE_TAC[candle_fs_hist_delta_hessian_real_length;
              candle_fs_hist_delta_hessian_real_rows] THEN
  DISCH_THEN (fun matrix_form -> ONCE_REWRITE_TAC[matrix_form]) THEN
  ONCE_REWRITE_TAC[LIST_EQ] THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  ONCE_REWRITE_TAC[LIST_EQ] THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ;
               candle_fs_hist_delta_hessian_component_real_def]);;

let candle_fs_hist_delta_hessian_component_real_in_range = prove
 (`!values i j.
     i < 6 /\ j < 6
     ==> candle_fs_hist_delta_hessian_component_real values i j =
         EL j (EL i (candle_fs_hist_delta_hessian_real values))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_fs_hist_delta_hessian_component_real_def]);;

let candle_fs_hist_delta_second_symmetric_components = prove
 (`!boxes (values:num->real).
     LENGTH boxes = 6 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 6)
     ==> candle_q_dim_jet_contains_components 6
           (candle_fs_hist_second_to_q
             (candle_fs_hist_delta_second boxes))
           (candle_fs_hist_delta_real values)
           (\i. EL i (candle_fs_hist_delta_gradient_real values))
           (candle_fs_hist_delta_hessian_component_real values)`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (SPECL [`boxes:((num#num)#(num#num))list`; `values:num->real`]
      candle_fs_hist_delta_second_components) THEN
  ASM_REWRITE_TAC[candle_q_dim_jet_contains_components_def] THEN
  MESON_TAC[candle_fs_hist_delta_hessian_component_real_in_range]);;

let candle_fs_hist_second_eta = prove
 (`!second.
     candle_fs_hist_second_make
       (candle_fs_hist_second_value second)
       (candle_fs_hist_second_gradient second)
       (candle_fs_hist_second_hessian second) = second`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_second_make_def;
              candle_fs_hist_second_value_def;
              candle_fs_hist_second_gradient_def;
              candle_fs_hist_second_hessian_def; FST; SND]);;

let candle_fs_hist_delta_second_data_shape = prove
 (`!boxes.
     LENGTH
       (candle_fs_hist_second_gradient
         (candle_fs_hist_delta_second boxes)) = 6 /\
     LENGTH
       (candle_fs_hist_second_hessian
         (candle_fs_hist_delta_second boxes)) = 6 /\
     ALL (\matrix_row. LENGTH matrix_row = 6)
       (candle_fs_hist_second_hessian
         (candle_fs_hist_delta_second boxes))`,
  REWRITE_TAC[candle_fs_hist_delta_second_def;
              candle_fs_hist_second_gradient_def;
              candle_fs_hist_second_hessian_def;
              candle_fs_hist_second_make_def;
              LET_DEF; LET_END_DEF; FST; SND] THEN
  REWRITE_TAC[candle_fs_hist_delta_gradient_def; LENGTH;
              candle_fs_angle_delta_hessian_length;
              candle_fs_hist_delta_hessian_interval_rows] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* Instantiate the general supplied-root chain rule with the complete checked
   delta jet.  The only remaining run-time obligations are the canonical
   positive endpoint forms and the supplied root enclosure; no componentwise
   arithmetic theorem is constructed for an accepted box. *)

let candle_fs_hist_root_delta_components = prove
 (`!boxes (values:num->real)
      input_lower input_upper root_lower root_upper.
     LENGTH boxes = 6 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 6) /\
     candle_fs_hist_second_value
       (candle_fs_hist_delta_second boxes) =
       ((input_lower,0),(input_upper,0)) /\
     0 < input_lower /\ input_lower <= input_upper /\
     0 < root_lower /\ root_lower <= root_upper /\
     &0 < candle_fs_hist_delta_real values /\
     candle_fs_interval_contains
       ((root_lower,0),(root_upper,0))
       (sqrt (candle_fs_hist_delta_real values))
     ==>
     candle_q_dim_jet_contains_components 6
       (candle_fs_hist_second_to_q
         (candle_fs_hist_second_sqrt_supplied
           (candle_fs_hist_delta_second boxes)
           ((root_lower,0),(root_upper,0))))
       (sqrt (candle_fs_hist_delta_real values))
       (\i.
          inv
            (sqrt (candle_fs_hist_delta_real values) +
             sqrt (candle_fs_hist_delta_real values)) *
          EL i (candle_fs_hist_delta_gradient_real values))
       (\i j.
          (--inv
            ((sqrt (candle_fs_hist_delta_real values) +
              sqrt (candle_fs_hist_delta_real values)) *
             (candle_fs_hist_delta_real values +
              candle_fs_hist_delta_real values))) *
            (EL i (candle_fs_hist_delta_gradient_real values) *
             EL j (candle_fs_hist_delta_gradient_real values)) +
          inv
            (sqrt (candle_fs_hist_delta_real values) +
             sqrt (candle_fs_hist_delta_real values)) *
            candle_fs_hist_delta_hessian_component_real values i j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      ((input_lower,0),(input_upper,0))
      (candle_fs_hist_delta_real values)`
  ASSUME_TAC THENL
   [MP_TAC
      (SPECL
        [`boxes:((num#num)#(num#num))list`; `values:num->real`]
        candle_fs_hist_delta_second_value_contains) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL2 candle_fs_interval_contains
      (candle_fs_hist_second_gradient
        (candle_fs_hist_delta_second boxes))
      (list_of_seq
        (\i. EL i (candle_fs_hist_delta_gradient_real values)) 6)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM candle_fs_hist_delta_gradient_real_list_of_seq] THEN
    MATCH_MP_TAC candle_fs_hist_delta_second_gradient_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL2 (ALL2 candle_fs_interval_contains)
      (candle_fs_hist_second_hessian
        (candle_fs_hist_delta_second boxes))
      (list_of_seq
        (\i. list_of_seq
          (\j. candle_fs_hist_delta_hessian_component_real values i j)
          6) 6)`
  ASSUME_TAC THENL
   [REWRITE_TAC
      [GSYM candle_fs_hist_delta_hessian_component_real_list_of_seq] THEN
    MATCH_MP_TAC candle_fs_hist_delta_second_hessian_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC (ISPEC `boxes:((num#num)#(num#num))list`
    candle_fs_hist_delta_second_data_shape) THEN
  STRIP_TAC THEN
  ONCE_REWRITE_TAC
    [GSYM (ISPEC `candle_fs_hist_delta_second boxes`
      candle_fs_hist_second_eta)] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC candle_fs_hist_second_sqrt_supplied_components THEN
  ASM_REWRITE_TAC[candle_fs_hist_delta_hessian_component_real_symmetric] THEN
  REWRITE_TAC
    [GSYM candle_fs_hist_delta_hessian_component_real_list_of_seq] THEN
  MATCH_MP_TAC candle_fs_hist_delta_second_hessian_contains THEN
  ASM_REWRITE_TAC[]);;

end;;
