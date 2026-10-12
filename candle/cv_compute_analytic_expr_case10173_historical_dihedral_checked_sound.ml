(* ========================================================================== *)
(* Case-10173 checked historical splice: auxiliary-root correspondence.      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_checked_compute.ml";;
needs "candle/cv_compute_analytic_expr_fixed_scale_angle_polynomials_sound.ml";;
needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_sound.ml";;

module Candle_cv_analytic_expr_case10173_historical_dihedral_checked_sound = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_whole_box_dim_taylor_sound;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_fixed_scale_invariant;;
open Candle_cv_analytic_expr_fixed_scale_angle_polynomials_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_root_four_x0_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_first_order_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_root_certificate_compute;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_checked_compute;;

let candle_case10173_hist_production_guard_def = new_definition
 `candle_case10173_hist_production_guard boxes roots =
    let center_environment = candle_fs_interval_list_of_q
      (candle_q_center_environment_list boxes) in
    let box_environment = candle_fs_interval_list_of_q boxes in
    let center_root_delta = candle_fs_interval_lookup 0 roots in
    let center_root_four_x0 = candle_fs_interval_lookup 1 roots in
    let box_root_delta = candle_fs_interval_lookup 2 roots in
    let box_root_four_x0 = candle_fs_interval_lookup 3 roots in
    let center_u126 = FST (candle_fs_hist_u126 center_environment) in
    let center_u135 = FST (candle_fs_hist_u135 center_environment) in
    let box_u126 = FST (candle_fs_hist_u126 box_environment) in
    let box_u135 = FST (candle_fs_hist_u135 box_environment) in
    let center_quotient = candle_fs_hist_quotient
      (candle_fs_hist_delta_x4_value_direct center_environment)
      center_root_delta center_root_four_x0 in
    let box_quotient = candle_fs_hist_quotient
      (candle_fs_hist_second_value
        (candle_fs_hist_delta_x4_second box_environment))
      box_root_delta box_root_four_x0 in
    candle_fs_hist_positive_product
      center_root_delta center_root_four_x0 /\
    candle_fs_hist_positive_product box_root_delta box_root_four_x0 /\
    candle_fs_hist_positive_interval center_u126 /\
    candle_fs_hist_positive_interval center_u135 /\
    candle_fs_hist_positive_product center_u126 center_u135 /\
    candle_fs_hist_positive_interval box_u126 /\
    candle_fs_hist_positive_interval box_u135 /\
    candle_fs_hist_positive_product box_u126 box_u135 /\
    candle_fs_hist_unit_interval center_quotient /\
    candle_fs_hist_unit_interval box_quotient /\
    candle_fs_hist_environment_nonnegative center_environment /\
    candle_fs_hist_environment_nonnegative box_environment`;;

let candle_cv_fs_hist_positive_interval_correct = prove
 (`!value.
     candle_cv_fs_hist_positive_interval (candle_cv_fs_interval value) =
     candle_cv_bool (candle_fs_hist_positive_interval value)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_hist_positive_interval_def;
              candle_fs_hist_positive_interval_def;
              candle_cv_fs_interval_def; candle_cv_lc_z_def;
              candle_cv_fs_hist_num_le_correct;
              candle_cv_fs_hist_bool_and_correct;
              candle_cv_fs_hist_num_equal_correct;
              candle_cv_fs_hist_num_less_correct;
              cexp_fst_def; cexp_snd_def;
              FST; SND]);;

let candle_cv_fs_hist_positive_product_correct = prove
 (`!left right.
     candle_cv_fs_hist_positive_product
       (candle_cv_fs_interval left) (candle_cv_fs_interval right) =
     candle_cv_bool (candle_fs_hist_positive_product left right)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_hist_positive_product_def;
              candle_fs_hist_positive_product_def;
              candle_cv_fs_interval_def; candle_cv_lc_z_def;
              candle_cv_fs_scale_correct;
              candle_cv_fs_hist_num_less_correct;
              cexp_fst_def; cexp_snd_def; cexp_mul_def; cexp_div_def;
              FST; SND]);;

let candle_cv_fs_raw_le_bool_correct = prove
 (`!left right.
     candle_cv_fs_raw_le
       (candle_cv_lc_z left) (candle_cv_lc_z right) =
     candle_cv_bool (candle_fs_raw_le left right)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_raw_le_correct; candle_cv_bool_def]);;

let candle_cv_fs_hist_unit_interval_correct = prove
 (`!value.
     candle_cv_fs_hist_unit_interval (candle_cv_fs_interval value) =
     candle_cv_bool (candle_fs_hist_unit_interval value)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_hist_unit_interval_def;
              candle_fs_hist_unit_interval_def;
              candle_cv_fs_interval_def;
              candle_cv_fs_one_correct;
              candle_cv_fs_raw_neg_correct;
              candle_cv_fs_raw_le_bool_correct;
              candle_cv_fs_hist_bool_not_correct;
              candle_cv_fs_hist_bool_and_correct;
              candle_fs_raw_le_real;
              candle_fs_raw_neg_real;
              candle_fs_real_def;
              candle_fs_scale_def;
              candle_lc_zreal_def;
              cexp_fst_def; cexp_snd_def;
              FST; SND] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_NOT_LE] THEN
  AP_TERM_TAC THEN REAL_ARITH_TAC);;

let candle_cv_fs_hist_environment_nonnegative_correct = prove
 (`!environment.
     candle_cv_fs_hist_environment_nonnegative
       (candle_cv_fs_interval_list environment) =
     candle_cv_bool
       (candle_fs_hist_environment_nonnegative environment)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_hist_environment_nonnegative_def;
              candle_fs_hist_environment_nonnegative_def;
              candle_cv_fs_interval_lookup_correct;
              candle_cv_fs_interval_def;
              candle_cv_fs_zero_correct;
              candle_cv_fs_raw_le_bool_correct;
              candle_cv_fs_hist_bool_and_correct;
              cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_hist_quotient_wrapper_correct = prove
 (`!delta_x4_interval root_delta root_four_x0.
     candle_cv_fs_hist_quotient
       (candle_cv_fs_interval delta_x4_interval)
       (candle_cv_fs_interval root_delta)
       (candle_cv_fs_interval root_four_x0) =
     candle_cv_fs_interval
       (candle_fs_hist_quotient
         delta_x4_interval root_delta root_four_x0)`,
  REWRITE_TAC[candle_cv_fs_hist_quotient_def;
              candle_cv_fs_hist_quotient_correct]);;

let candle_cv_case10173_hist_production_guard_correct = prove
 (`!boxes roots.
     candle_cv_case10173_hist_production_guard
       (candle_cv_q_interval_list boxes)
       (candle_cv_fs_interval_list roots) =
     candle_cv_bool
       (candle_case10173_hist_production_guard boxes roots)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_case10173_hist_production_guard_def;
              candle_case10173_hist_production_guard_def;
              candle_cv_q_center_environment_list_correct;
              candle_cv_fs_interval_list_of_q_correct;
              candle_cv_fs_interval_lookup_correct;
              candle_cv_fs_hist_u126_correct;
              candle_cv_fs_hist_u135_correct;
              candle_cv_fs_hist_u_fst_correct;
              candle_cv_fs_hist_delta_x4_value_direct_correct;
              candle_cv_fs_hist_delta_x4_second_correct;
              candle_cv_fs_hist_second_value_correct;
              candle_cv_fs_hist_quotient_wrapper_correct;
              candle_cv_fs_hist_positive_product_correct;
              candle_cv_fs_hist_positive_interval_correct;
              candle_cv_fs_hist_unit_interval_correct;
              candle_cv_fs_hist_environment_nonnegative_correct;
              candle_cv_fs_zero_correct;
              candle_cv_fs_raw_le_correct;
              candle_cv_fs_hist_bool_and_correct;
              LET_DEF; LET_END_DEF]);;

let candle_fs_hist_positive_root_certificate_def = new_definition
 `candle_fs_hist_positive_root_certificate
      (input:((num#num)#(num#num)))
      (root_value:((num#num)#(num#num))) <=>
    SND (FST input) = 0 /\ SND (SND input) = 0 /\
    SND (FST root_value) = 0 /\ SND (SND root_value) = 0 /\
    candle_fs_hist_root_certificate
      (FST (FST input)) (FST (SND input))
      (FST (FST root_value)) (FST (SND root_value))`;;

let candle_cv_fs_hist_positive_root_certificate_components_correct = prove
 (`!input_lower input_lower_neg input_upper input_upper_neg
      root_lower root_lower_neg root_upper root_upper_neg.
     candle_cv_fs_hist_positive_root_certificate
       (candle_cv_fs_interval
         ((input_lower,input_lower_neg),(input_upper,input_upper_neg)))
       (candle_cv_fs_interval
         ((root_lower,root_lower_neg),(root_upper,root_upper_neg))) =
     candle_cv_bool
       (candle_fs_hist_positive_root_certificate
         ((input_lower,input_lower_neg),(input_upper,input_upper_neg))
         ((root_lower,root_lower_neg),(root_upper,root_upper_neg)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_hist_positive_root_certificate_def;
              candle_fs_hist_positive_root_certificate_def;
              candle_cv_fs_hist_root_certificate_def;
              candle_fs_hist_root_certificate_def;
              candle_cv_fs_interval_def; candle_cv_lc_z_def;
              cexp_fst_def; cexp_snd_def; cexp_mul_def;
              candle_cv_fs_scale_correct;
              candle_cv_fs_hist_num_ispair_correct;
              candle_cv_fs_hist_pair_ispair_correct;
              candle_cv_fs_hist_num_equal_correct;
              candle_cv_fs_hist_bool_not_correct;
              candle_cv_fs_hist_bool_and_correct;
              candle_cv_fs_hist_num_less_correct;
              candle_cv_fs_hist_num_le_correct;
              candle_cv_bool_def;
              FST; SND; LET_DEF; LET_END_DEF;
              ARITH_RULE `1 = SUC 0`; injectivity "cval"] THEN
  REWRITE_TAC[candle_cv_fs_hist_bool_not_def;
              candle_cv_fs_hist_bool_and_def] THEN
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`] THEN
  REPEAT
   (COND_CASES_TAC THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 = SUC 0`; cexp_if_def]) THEN
  REWRITE_TAC[cexp_if_def] THEN
  REWRITE_TAC[cexp_if_def] THEN
  REWRITE_TAC[cexp_if_def] THEN
  REWRITE_TAC[cexp_if_def] THEN
  REWRITE_TAC[cexp_if_def] THEN
  REWRITE_TAC[cexp_if_def] THEN
  REWRITE_TAC[cexp_if_def] THEN
  REWRITE_TAC[cexp_if_def] THEN
  ARITH_TAC);;

let candle_cv_fs_hist_positive_root_certificate_correct = prove
 (`!input root_value.
     candle_cv_fs_hist_positive_root_certificate
       (candle_cv_fs_interval input)
       (candle_cv_fs_interval root_value) =
     candle_cv_bool
       (candle_fs_hist_positive_root_certificate input root_value)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  MATCH_ACCEPT_TAC
    candle_cv_fs_hist_positive_root_certificate_components_correct);;

let candle_cv_fs_hist_root_list_check_four_correct = prove
 (`!input0 input1 input2 input3 root0 root1 root2 root3.
     candle_cv_fs_hist_root_list_check
       (candle_cv_fs_interval_list [input0;input1;input2;input3])
       (candle_cv_fs_interval_list [root0;root1;root2;root3]) =
     candle_cv_bool
       (candle_fs_hist_positive_root_certificate input0 root0 /\
        candle_fs_hist_positive_root_certificate input1 root1 /\
        candle_fs_hist_positive_root_certificate input2 root2 /\
        candle_fs_hist_positive_root_certificate input3 root3)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_fs_interval_list_def;
     candle_cv_fs_hist_root_list_check_def;
     candle_cv_fs_hist_positive_root_certificate_correct;
     candle_cv_fs_hist_bool_and_def; candle_cv_bool_def;
     cexp_eq_def; injectivity "cval"; injectivity "num";
     ARITH_RULE `1 = SUC 0`] THEN
  REPEAT
   (COND_CASES_TAC THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 = SUC 0`; cexp_if_def]));;

let candle_case10173_hist_root_inputs_def = new_definition
 `candle_case10173_hist_root_inputs boxes =
    let center_environment = candle_fs_interval_list_of_q
      (candle_q_center_environment_list boxes) in
    let box_environment = candle_fs_interval_list_of_q boxes in
    [candle_fs_angle_delta_value center_environment;
     candle_fs_angle_interval_scale 4
       (candle_fs_interval_lookup 0 center_environment);
     candle_fs_hist_second_value
       (candle_fs_hist_delta_second box_environment);
     candle_fs_angle_interval_scale 4
       (candle_fs_interval_lookup 0 box_environment)]`;;

let candle_cv_case10173_hist_root_inputs_correct = prove
 (`!boxes.
     candle_cv_case10173_hist_root_inputs
       (candle_cv_q_interval_list boxes) =
     candle_cv_fs_interval_list
       (candle_case10173_hist_root_inputs boxes)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_case10173_hist_root_inputs_def;
              candle_case10173_hist_root_inputs_def;
              candle_cv_q_center_environment_list_correct;
              candle_cv_fs_interval_list_of_q_correct;
              candle_cv_fs_angle_delta_value_correct;
              candle_cv_fs_hist_delta_second_correct;
              candle_cv_fs_hist_second_value_correct;
              candle_cv_fs_interval_lookup_correct;
              candle_cv_fs_angle_interval_scale_correct;
              candle_cv_fs_interval_list_def;
              LET_DEF; LET_END_DEF]);;

let candle_case10173_hist_root_record_valid_def = new_definition
 `candle_case10173_hist_root_record_valid boxes roots <=>
    ALL2 candle_fs_hist_positive_root_certificate
      (candle_case10173_hist_root_inputs boxes) roots`;;

let candle_cv_case10173_hist_root_record_check_correct = prove
 (`!boxes root0 root1 root2 root3.
     candle_cv_case10173_hist_root_record_check
       (candle_cv_q_interval_list boxes)
       (candle_cv_fs_interval_list [root0;root1;root2;root3]) =
     candle_cv_bool
       (candle_case10173_hist_root_record_valid boxes
         [root0;root1;root2;root3])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_case10173_hist_root_record_check_def;
              candle_case10173_hist_root_record_valid_def;
              candle_cv_case10173_hist_root_inputs_correct;
              candle_case10173_hist_root_inputs_def;
              candle_cv_fs_hist_root_list_check_four_correct;
              ALL2; LET_DEF; LET_END_DEF]);;

let candle_fs_hist_positive_root_certificate_components_contains = prove
 (`!input_lower input_lower_neg input_upper input_upper_neg
      root_lower root_lower_neg root_upper root_upper_neg x.
     candle_fs_hist_positive_root_certificate
       ((input_lower,input_lower_neg),(input_upper,input_upper_neg))
       ((root_lower,root_lower_neg),(root_upper,root_upper_neg)) /\
     candle_fs_interval_contains
       ((input_lower,input_lower_neg),(input_upper,input_upper_neg)) x
     ==> candle_fs_interval_contains
       ((root_lower,root_lower_neg),(root_upper,root_upper_neg)) (sqrt x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_positive_root_certificate_def; FST; SND] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC
    (SPECL
      [`input_lower:num`; `input_upper:num`;
       `root_lower:num`; `root_upper:num`; `x:real`]
      candle_fs_hist_root_certificate_contains) THEN
  ASM_MESON_TAC[]);;

let candle_fs_hist_positive_root_certificate_contains = prove
 (`!input root_value x.
     candle_fs_hist_positive_root_certificate input root_value /\
     candle_fs_interval_contains input x
     ==> candle_fs_interval_contains root_value (sqrt x)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  MATCH_ACCEPT_TAC
    candle_fs_hist_positive_root_certificate_components_contains);;

(* The authenticated input interval also proves the strict positivity needed
   by the analytic square-root and reciprocal semantics. *)

let candle_fs_hist_positive_root_certificate_input_positive_components = prove
 (`!input_lower input_lower_neg input_upper input_upper_neg
      root_lower root_lower_neg root_upper root_upper_neg x.
     candle_fs_hist_positive_root_certificate
       ((input_lower,input_lower_neg),(input_upper,input_upper_neg))
       ((root_lower,root_lower_neg),(root_upper,root_upper_neg)) /\
     candle_fs_interval_contains
       ((input_lower,input_lower_neg),(input_upper,input_upper_neg)) x
     ==> &0 < x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_positive_root_certificate_def;
              candle_fs_hist_root_certificate_def;
              candle_fs_interval_contains_def;
              candle_fs_real_def; candle_lc_zreal_def;
              FST; SND; REAL_SUB_RZERO] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(input_lower:num)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LT];
    SUBGOAL_THEN `&0 < &(candle_fs_scale)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LT; candle_fs_scale_pos];
      SUBGOAL_THEN
       `&(input_lower:num) / &(candle_fs_scale) <= x`
      ASSUME_TAC THENL
       [UNDISCH_TAC
         `(&(input_lower:num) - &(input_lower_neg:num)) /
          &(candle_fs_scale) <= x` THEN
        ASM_REWRITE_TAC[REAL_SUB_RZERO];
        SUBGOAL_THEN
         `&0 < &(input_lower:num) / &(candle_fs_scale)` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
          ASM_REAL_ARITH_TAC]]]]);;

let candle_fs_hist_positive_root_certificate_input_positive = prove
 (`!input root_value x.
     candle_fs_hist_positive_root_certificate input root_value /\
     candle_fs_interval_contains input x
     ==> &0 < x`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  MATCH_ACCEPT_TAC
    candle_fs_hist_positive_root_certificate_input_positive_components);;

let candle_case10173_hist_root_record_valid_components = prove
 (`!boxes center_root_delta center_root_four_x0
      box_root_delta box_root_four_x0.
     candle_case10173_hist_root_record_valid boxes
       [center_root_delta;center_root_four_x0;
        box_root_delta;box_root_four_x0] <=>
     let center_environment = candle_fs_interval_list_of_q
       (candle_q_center_environment_list boxes) in
     let box_environment = candle_fs_interval_list_of_q boxes in
     candle_fs_hist_positive_root_certificate
       (candle_fs_angle_delta_value center_environment)
       center_root_delta /\
     candle_fs_hist_positive_root_certificate
       (candle_fs_angle_interval_scale 4
         (candle_fs_interval_lookup 0 center_environment))
       center_root_four_x0 /\
     candle_fs_hist_positive_root_certificate
       (candle_fs_hist_second_value
         (candle_fs_hist_delta_second box_environment))
       box_root_delta /\
     candle_fs_hist_positive_root_certificate
       (candle_fs_angle_interval_scale 4
         (candle_fs_interval_lookup 0 box_environment))
       box_root_four_x0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_case10173_hist_root_record_valid_def;
              candle_case10173_hist_root_inputs_def;
              ALL2; LET_DEF; LET_END_DEF]);;

(* Keep the checked-root contract independent of the substantially larger
   first-order reference stack.  This is the value-only containment fact
   needed to turn the authenticated center delta interval into a semantic
   positivity fact. *)

let candle_case10173_hist_angle_delta_value_contains = prove
 (`!environment (values:num->real).
     LENGTH environment = 6 /\
     ALL2 candle_fs_interval_contains environment (list_of_seq values 6)
     ==> candle_fs_interval_contains
           (candle_fs_angle_delta_value environment)
           (candle_fs_hist_delta_real values)`,
  REPEAT STRIP_TAC THEN
  let lookup_tac =
    MATCH_MP_TAC candle_fs_hist_six_lookup_contains THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC in
  let signed_lookup_tac =
    FIRST
     [MATCH_MP_TAC candle_fs_interval_neg_sound THEN lookup_tac;
      lookup_tac] in
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_angle_interval_sum
        [candle_fs_interval_neg (candle_fs_interval_lookup 0 environment);
         candle_fs_interval_lookup 1 environment;
         candle_fs_interval_lookup 2 environment;
         candle_fs_interval_neg (candle_fs_interval_lookup 3 environment);
         candle_fs_interval_lookup 4 environment;
         candle_fs_interval_lookup 5 environment])
      (ITLIST (\x total:real. x + total)
        [--(values 0);values 1;values 2;
         --(values 3);values 4;values 5] (&0))`
  (LABEL_TAC "l0") THENL
   [MATCH_MP_TAC candle_fs_hist_interval_sum_contains THEN
    REWRITE_TAC[ALL2] THEN
    REPEAT CONJ_TAC THEN signed_lookup_tac;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_angle_interval_sum
        [candle_fs_interval_lookup 0 environment;
         candle_fs_interval_neg (candle_fs_interval_lookup 1 environment);
         candle_fs_interval_lookup 2 environment;
         candle_fs_interval_lookup 3 environment;
         candle_fs_interval_neg (candle_fs_interval_lookup 4 environment);
         candle_fs_interval_lookup 5 environment])
      (ITLIST (\x total:real. x + total)
        [values 0;--(values 1);values 2;values 3;
         --(values 4);values 5] (&0))`
  (LABEL_TAC "l1") THENL
   [MATCH_MP_TAC candle_fs_hist_interval_sum_contains THEN
    REWRITE_TAC[ALL2] THEN
    REPEAT CONJ_TAC THEN signed_lookup_tac;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_angle_interval_sum
        [candle_fs_interval_lookup 0 environment;
         candle_fs_interval_lookup 1 environment;
         candle_fs_interval_neg (candle_fs_interval_lookup 2 environment);
         candle_fs_interval_lookup 3 environment;
         candle_fs_interval_lookup 4 environment;
         candle_fs_interval_neg (candle_fs_interval_lookup 5 environment)])
      (ITLIST (\x total:real. x + total)
        [values 0;values 1;--(values 2);values 3;values 4;
         --(values 5)] (&0))`
  (LABEL_TAC "l2") THENL
   [MATCH_MP_TAC candle_fs_hist_interval_sum_contains THEN
    REWRITE_TAC[ALL2] THEN
    REPEAT CONJ_TAC THEN signed_lookup_tac;
    ALL_TAC] THEN
  REWRITE_TAC[candle_fs_angle_delta_value_def;
              candle_fs_hist_delta_real_def;
              LET_DEF; LET_END_DEF] THEN
  MATCH_MP_TAC candle_fs_hist_interval_sum_contains THEN
  REWRITE_TAC[ALL2] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
      CONJ_TAC THEN lookup_tac;
      USE_THEN "l0" ACCEPT_TAC];
    MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
      CONJ_TAC THEN lookup_tac;
      USE_THEN "l1" ACCEPT_TAC];
    MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
      CONJ_TAC THEN lookup_tac;
      USE_THEN "l2" ACCEPT_TAC];
    MATCH_MP_TAC candle_fs_interval_neg_sound THEN
    MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
      CONJ_TAC THEN lookup_tac;
      lookup_tac];
    MATCH_MP_TAC candle_fs_interval_neg_sound THEN
    MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
      CONJ_TAC THEN lookup_tac;
      lookup_tac];
    MATCH_MP_TAC candle_fs_interval_neg_sound THEN
    MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
      CONJ_TAC THEN lookup_tac;
      lookup_tac];
    MATCH_MP_TAC candle_fs_interval_neg_sound THEN
    MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
      CONJ_TAC THEN lookup_tac;
      lookup_tac]]);;

let candle_case10173_q_box_center_vector_list_six = prove
 (`!boxes.
     LENGTH boxes = 6
     ==>
     list_of_seq
       (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1)) 6 =
     MAP (\box. candle_q_real (candle_q_midpoint box)) boxes`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; LENGTH_MAP] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `k + 1 IN 1..dimindex (:6)` ASSUME_TAC THENL
   [CONV_TAC (ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[EL_LIST_OF_SEQ; EL_MAP;
                 candle_q_box_center_vector_component; ADD_SUB]]);;

let candle_case10173_fs_center_environment_contains_six = prove
 (`!boxes.
     LENGTH boxes = 6
     ==>
     ALL2 candle_fs_interval_contains
       (candle_fs_interval_list_of_q
         (candle_q_center_environment_list boxes))
       (list_of_seq
         (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1)) 6)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC candle_fs_interval_list_of_q_contains THEN
  MP_TAC (SPEC
    `boxes:(((num#num)#num)#((num#num)#num))list`
    candle_q_center_environment_list_contains) THEN
  ASM_SIMP_TAC[GSYM candle_case10173_q_box_center_vector_list_six]);;

let candle_case10173_q_box_stack_contains_vector_six = prove
 (`!boxes (z:real^6).
     LENGTH boxes = 6 /\
     z IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
     ==>
     candle_q_stack_contains boxes
       (list_of_seq (\k. z$(k + 1)) 6)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
   (CONJUNCTS_THEN2
     (LABEL_TAC "box_length") (LABEL_TAC "z_in")) THEN
  REWRITE_TAC[candle_q_stack_contains_all2] THEN
  SUBGOAL_THEN
   `(boxes:(((num#num)#num)#((num#num)#num))list) =
    list_of_seq (\k. EL k boxes) 6`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_LIST_OF_SEQ] THEN
    USE_THEN "box_length" ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[candle_all2_list_of_seq] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `k + 1 IN 1..dimindex (:6)` ASSUME_TAC THENL
   [CONV_TAC (ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "z_in" (MP_TAC o REWRITE_RULE[IN_INTERVAL]) THEN
  DISCH_THEN (MP_TAC o SPEC `k + 1`) THEN
  DISCH_THEN
   (fun th -> MP_TAC
     (MATCH_MP th
       (REWRITE_RULE[IN_NUMSEG]
         (ASSUME `k + 1 IN 1..dimindex (:6)`)))) THEN
  ASM_SIMP_TAC[candle_q_interval_contains_def;
               candle_q_box_lower_vector_component;
               candle_q_box_upper_vector_component; ADD_SUB]);;

(* A valid four-root record is a semantic certificate for both positive
   radicands at the center and at every point of the job box.  These facts are
   precisely the source-regularity part of the historical splice contract. *)

let candle_case10173_hist_root_record_semantics = prove
 (`!boxes center_root_delta center_root_four_x0
      box_root_delta box_root_four_x0.
     LENGTH boxes = 6 /\
     candle_case10173_hist_root_record_valid boxes
       [center_root_delta;center_root_four_x0;
        box_root_delta;box_root_four_x0]
     ==>
     let center_values =
       \k. (candle_q_box_center_vector boxes : real^6)$(k + 1) in
     &0 < candle_fs_hist_delta_real center_values /\
     &0 < candle_fs_hist_four_x0_real center_values /\
     candle_fs_interval_contains center_root_delta
       (sqrt (candle_fs_hist_delta_real center_values)) /\
     candle_fs_interval_contains center_root_four_x0
       (sqrt (candle_fs_hist_four_x0_real center_values)) /\
     (!(p:real^6). p IN interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]
        ==>
        &0 < candle_fs_hist_delta_real (\k. p$(k + 1)) /\
        &0 < candle_fs_hist_four_x0_real (\k. p$(k + 1)) /\
        candle_fs_interval_contains box_root_delta
          (sqrt (candle_fs_hist_delta_real (\k. p$(k + 1)))) /\
        candle_fs_interval_contains box_root_four_x0
          (sqrt (candle_fs_hist_four_x0_real (\k. p$(k + 1)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
    (SPECL
      [`boxes:(((num#num)#num)#((num#num)#num))list`;
       `center_root_delta:(num#num)#(num#num)`;
       `center_root_four_x0:(num#num)#(num#num)`;
       `box_root_delta:(num#num)#(num#num)`;
       `box_root_four_x0:(num#num)#(num#num)`]
      candle_case10173_hist_root_record_valid_components) THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ALL2 candle_fs_interval_contains
      (candle_fs_interval_list_of_q
        (candle_q_center_environment_list boxes))
      (list_of_seq
        (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1)) 6)`
  (LABEL_TAC "center_contains") THENL
   [MATCH_MP_TAC candle_case10173_fs_center_environment_contains_six THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_angle_delta_value
        (candle_fs_interval_list_of_q
          (candle_q_center_environment_list boxes)))
      (candle_fs_hist_delta_real
        (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1)))`
  (LABEL_TAC "center_delta_contains") THENL
   [MATCH_MP_TAC candle_case10173_hist_angle_delta_value_contains THEN
    ASM_REWRITE_TAC[candle_fs_interval_list_of_q_length;
                    candle_q_center_environment_list_length];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_angle_interval_scale 4
        (candle_fs_interval_lookup 0
          (candle_fs_interval_list_of_q
            (candle_q_center_environment_list boxes))))
      (candle_fs_hist_four_x0_real
        (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1)))`
  (LABEL_TAC "center_four_contains") THENL
   [REWRITE_TAC[candle_fs_hist_four_x0_real_def] THEN
    MATCH_MP_TAC candle_fs_angle_interval_scale_contains THEN
    MATCH_MP_TAC candle_fs_hist_six_lookup_contains THEN
    ASM_REWRITE_TAC[candle_fs_interval_list_of_q_length;
                    candle_q_center_environment_list_length] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC
      (SPECL
        [`candle_fs_angle_delta_value
            (candle_fs_interval_list_of_q
              (candle_q_center_environment_list boxes))`;
         `center_root_delta:(num#num)#(num#num)`;
         `candle_fs_hist_delta_real
            (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1))`]
        candle_fs_hist_positive_root_certificate_input_positive) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC
      (SPECL
        [`candle_fs_angle_interval_scale 4
            (candle_fs_interval_lookup 0
              (candle_fs_interval_list_of_q
                (candle_q_center_environment_list boxes)))`;
         `center_root_four_x0:(num#num)#(num#num)`;
         `candle_fs_hist_four_x0_real
            (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1))`]
        candle_fs_hist_positive_root_certificate_input_positive) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC
      (SPECL
        [`candle_fs_angle_delta_value
            (candle_fs_interval_list_of_q
              (candle_q_center_environment_list boxes))`;
         `center_root_delta:(num#num)#(num#num)`;
         `candle_fs_hist_delta_real
            (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1))`]
        candle_fs_hist_positive_root_certificate_contains) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC
      (SPECL
        [`candle_fs_angle_interval_scale 4
            (candle_fs_interval_lookup 0
              (candle_fs_interval_list_of_q
                (candle_q_center_environment_list boxes)))`;
         `center_root_four_x0:(num#num)#(num#num)`;
         `candle_fs_hist_four_x0_real
            (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1))`]
        candle_fs_hist_positive_root_certificate_contains) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `p:real^6` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `ALL2 candle_fs_interval_contains
        (candle_fs_interval_list_of_q boxes)
        (list_of_seq (\k. (p:real^6)$(k + 1)) 6)`
    (LABEL_TAC "box_contains") THENL
     [MATCH_MP_TAC candle_fs_interval_list_of_q_contains THEN
      MATCH_MP_TAC candle_case10173_q_box_stack_contains_vector_six THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `candle_fs_interval_contains
        (candle_fs_hist_second_value
          (candle_fs_hist_delta_second
            (candle_fs_interval_list_of_q boxes)))
        (candle_fs_hist_delta_real (\k. (p:real^6)$(k + 1)))`
    (LABEL_TAC "box_delta_contains") THENL
     [MATCH_MP_TAC candle_fs_hist_delta_second_value_contains THEN
      ASM_REWRITE_TAC[candle_fs_interval_list_of_q_length];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `candle_fs_interval_contains
        (candle_fs_angle_interval_scale 4
          (candle_fs_interval_lookup 0
            (candle_fs_interval_list_of_q boxes)))
        (candle_fs_hist_four_x0_real (\k. (p:real^6)$(k + 1)))`
    (LABEL_TAC "box_four_contains") THENL
     [REWRITE_TAC[candle_fs_hist_four_x0_real_def] THEN
      MATCH_MP_TAC candle_fs_angle_interval_scale_contains THEN
      MATCH_MP_TAC candle_fs_hist_six_lookup_contains THEN
      ASM_REWRITE_TAC[candle_fs_interval_list_of_q_length] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC
        (SPECL
          [`candle_fs_hist_second_value
              (candle_fs_hist_delta_second
                (candle_fs_interval_list_of_q boxes))`;
           `box_root_delta:(num#num)#(num#num)`;
           `candle_fs_hist_delta_real (\k. (p:real^6)$(k + 1))`]
          candle_fs_hist_positive_root_certificate_input_positive) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC
        (SPECL
          [`candle_fs_angle_interval_scale 4
              (candle_fs_interval_lookup 0
                (candle_fs_interval_list_of_q boxes))`;
           `box_root_four_x0:(num#num)#(num#num)`;
           `candle_fs_hist_four_x0_real (\k. (p:real^6)$(k + 1))`]
          candle_fs_hist_positive_root_certificate_input_positive) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC
        (SPECL
          [`candle_fs_hist_second_value
              (candle_fs_hist_delta_second
                (candle_fs_interval_list_of_q boxes))`;
           `box_root_delta:(num#num)#(num#num)`;
           `candle_fs_hist_delta_real (\k. (p:real^6)$(k + 1))`]
          candle_fs_hist_positive_root_certificate_contains) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC
        (SPECL
          [`candle_fs_angle_interval_scale 4
              (candle_fs_interval_lookup 0
                (candle_fs_interval_list_of_q boxes))`;
           `box_root_four_x0:(num#num)#(num#num)`;
           `candle_fs_hist_four_x0_real (\k. (p:real^6)$(k + 1))`]
          candle_fs_hist_positive_root_certificate_contains) THEN
      ASM_REWRITE_TAC[]]]);;

end;;
