(* ========================================================================== *)
(* Actual historical input jets packaged for the universal dihedral contract. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_composition_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_dihedral_reference_sound = struct

open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_delta_root_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_delta_x4_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_root_four_x0_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_composition_sound;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_sound;;

(* The supplied square-root constructor preserves the six-entry gradient and
   always builds the checked six-by-six historical square-root Hessian. *)

let candle_fs_hist_second_sqrt_supplied_to_q_shape = prove
 (`!input root_value.
     LENGTH (candle_fs_hist_second_gradient input) = 6
     ==> candle_q_dim_jet_shape 6
           (candle_fs_hist_second_to_q
           (candle_fs_hist_second_sqrt_supplied input root_value))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_fs_hist_second_gradient_def]) THEN
  REWRITE_TAC[candle_fs_hist_second_to_q_def;
              candle_fs_first_to_q_shape;
              candle_fs_hist_second_sqrt_supplied_def;
              candle_fs_hist_second_make_def;
              candle_fs_hist_second_gradient_def;
              candle_fs_hist_second_hessian_def;
              candle_fs_first_make_def;
              candle_fs_first_gradient_def;
              LET_DEF; LET_END_DEF; FST; SND;
              candle_fsn_interval_list_scale_length] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_ACCEPT_TAC candle_fs_hist_sqrt_hessian_shape);;

let candle_fs_hist_root_delta_to_q_shape = prove
 (`!boxes root_value.
     candle_q_dim_jet_shape 6
       (candle_fs_hist_second_to_q
         (candle_fs_hist_second_sqrt_supplied
           (candle_fs_hist_delta_second boxes) root_value))`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC candle_fs_hist_second_sqrt_supplied_to_q_shape THEN
  MP_TAC (ISPEC `boxes:((num#num)#(num#num))list`
    candle_fs_hist_delta_second_data_shape) THEN
  MESON_TAC[]);;

let candle_fs_hist_root_four_x0_to_q_shape = prove
 (`!boxes root_value.
     LENGTH boxes = 6
     ==> candle_q_dim_jet_shape 6
       (candle_fs_hist_second_to_q
         (candle_fs_hist_second_sqrt_supplied
           (candle_fs_hist_four_x0_second boxes) root_value))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC candle_fs_hist_second_sqrt_supplied_to_q_shape THEN
  MP_TAC (ISPEC `boxes:((num#num)#(num#num))list`
    candle_fs_hist_four_x0_second_data_shape) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let candle_fs_hist_delta_x4_real_jet_def = new_definition
 `candle_fs_hist_delta_x4_real_jet values =
    candle_hist_real_jet_make
      (candle_fs_hist_delta_x4_real values)
      (candle_fs_hist_delta_x4_derivative values)
      candle_fs_hist_delta_x4_hessian_component_real`;;

let candle_fs_hist_root_delta_real_jet_def = new_definition
 `candle_fs_hist_root_delta_real_jet values =
    candle_hist_real_jet_make
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
           candle_fs_hist_delta_hessian_component_real values i j)`;;

let candle_fs_hist_root_four_x0_real_jet_def = new_definition
 `candle_fs_hist_root_four_x0_real_jet values =
    candle_hist_real_jet_make
      (sqrt (candle_fs_hist_four_x0_real values))
      (\i.
         inv
           (sqrt (candle_fs_hist_four_x0_real values) +
            sqrt (candle_fs_hist_four_x0_real values)) *
         candle_fs_hist_four_x0_gradient_real i)
      (\i j.
         (--inv
           ((sqrt (candle_fs_hist_four_x0_real values) +
             sqrt (candle_fs_hist_four_x0_real values)) *
            (candle_fs_hist_four_x0_real values +
             candle_fs_hist_four_x0_real values))) *
           (candle_fs_hist_four_x0_gradient_real i *
            candle_fs_hist_four_x0_gradient_real j) +
         inv
           (sqrt (candle_fs_hist_four_x0_real values) +
            sqrt (candle_fs_hist_four_x0_real values)) *
           candle_fs_hist_four_x0_hessian_real i j)`;;

let candle_fs_hist_delta_x4_real_jet_components = prove
 (`!boxes values.
     LENGTH boxes = 6 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 6)
     ==> candle_q_dim_jet_contains_components 6
           (candle_fs_hist_second_to_q
             (candle_fs_hist_delta_x4_second boxes))
           (candle_hist_real_jet_value
             (candle_fs_hist_delta_x4_real_jet values))
           (candle_hist_real_jet_gradient
             (candle_fs_hist_delta_x4_real_jet values))
           (candle_hist_real_jet_hessian
             (candle_fs_hist_delta_x4_real_jet values))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_delta_x4_real_jet_def;
              candle_hist_real_jet_make_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_hessian_def; FST; SND] THEN
  MATCH_ACCEPT_TAC candle_fs_hist_delta_x4_second_components);;

let candle_fs_hist_root_delta_real_jet_components = prove
 (`!boxes values input_lower input_upper root_lower root_upper.
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
     ==> candle_q_dim_jet_contains_components 6
       (candle_fs_hist_second_to_q
         (candle_fs_hist_second_sqrt_supplied
           (candle_fs_hist_delta_second boxes)
           ((root_lower,0),(root_upper,0))))
       (candle_hist_real_jet_value
         (candle_fs_hist_root_delta_real_jet values))
       (candle_hist_real_jet_gradient
         (candle_fs_hist_root_delta_real_jet values))
       (candle_hist_real_jet_hessian
         (candle_fs_hist_root_delta_real_jet values))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_root_delta_real_jet_def;
              candle_hist_real_jet_make_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_hessian_def; FST; SND] THEN
  MATCH_ACCEPT_TAC candle_fs_hist_root_delta_components);;

let candle_fs_hist_root_four_x0_real_jet_components = prove
 (`!boxes values input_lower input_upper root_lower root_upper.
     LENGTH boxes = 6 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 6) /\
     candle_fs_hist_second_value
       (candle_fs_hist_four_x0_second boxes) =
       ((input_lower,0),(input_upper,0)) /\
     0 < input_lower /\ input_lower <= input_upper /\
     0 < root_lower /\ root_lower <= root_upper /\
     &0 < candle_fs_hist_four_x0_real values /\
     candle_fs_interval_contains
       ((root_lower,0),(root_upper,0))
       (sqrt (candle_fs_hist_four_x0_real values))
     ==> candle_q_dim_jet_contains_components 6
       (candle_fs_hist_second_to_q
         (candle_fs_hist_second_sqrt_supplied
           (candle_fs_hist_four_x0_second boxes)
           ((root_lower,0),(root_upper,0))))
       (candle_hist_real_jet_value
         (candle_fs_hist_root_four_x0_real_jet values))
       (candle_hist_real_jet_gradient
         (candle_fs_hist_root_four_x0_real_jet values))
       (candle_hist_real_jet_hessian
         (candle_fs_hist_root_four_x0_real_jet values))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_root_four_x0_real_jet_def;
              candle_hist_real_jet_make_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_hessian_def; FST; SND] THEN
  MATCH_ACCEPT_TAC candle_fs_hist_root_four_x0_components);;

end;;
