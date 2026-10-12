(* ========================================================================== *)
(* Case-10173 checked historical splice: auxiliary-root correspondence.      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_checked_compute.ml";;
needs "candle/cv_compute_analytic_expr_fixed_scale_angle_polynomials_sound.ml";;
needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_sound.ml";;

module Candle_cv_analytic_expr_case10173_historical_dihedral_checked_sound = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_fixed_scale_angle_polynomials_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_root_certificate_compute;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_checked_compute;;

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

end;;
