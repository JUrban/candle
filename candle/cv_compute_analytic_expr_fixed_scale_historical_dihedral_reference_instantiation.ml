(* ========================================================================== *)
(* Historical dihedral sources instantiated in the generic analytic contract. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_reference_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_dihedral_reference_instantiation = struct

open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_delta_x4_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_root_four_x0_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_composition_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_reference_sound;;
open Candle_cv_analytic_expr_fixed_scale_sound;;

(* This is an exact analytic reference boundary.  The low-work specialized
   instruction must subsequently be proved to enclose these same components;
   it is not replaced by this generic evaluator. *)

let candle_fs_hist_delta_x4_q_jet_def = new_definition
 `candle_fs_hist_delta_x4_q_jet boxes =
    candle_fs_hist_second_to_q
      (candle_fs_hist_delta_x4_second boxes)`;;

let candle_fs_hist_root_delta_q_jet_def = new_definition
 `candle_fs_hist_root_delta_q_jet boxes root_lower root_upper =
    candle_fs_hist_second_to_q
      (candle_fs_hist_second_sqrt_supplied
        (candle_fs_hist_delta_second boxes)
        ((root_lower,0),(root_upper,0)))`;;

let candle_fs_hist_root_four_x0_q_jet_def = new_definition
 `candle_fs_hist_root_four_x0_q_jet boxes root_lower root_upper =
    candle_fs_hist_second_to_q
      (candle_fs_hist_second_sqrt_supplied
        (candle_fs_hist_four_x0_second boxes)
        ((root_lower,0),(root_upper,0)))`;;

let candle_fs_hist_reference_dihedral_q_jet_def = new_definition
 `candle_fs_hist_reference_dihedral_q_jet boxes
      root_delta_lower root_delta_upper
      root_four_x0_lower root_four_x0_upper =
    candle_q_hist_dihedral_jet (candle_fs_interval_list_to_q boxes)
      (candle_fs_hist_delta_x4_q_jet boxes)
      (candle_fs_hist_root_delta_q_jet
        boxes root_delta_lower root_delta_upper)
      (candle_fs_hist_root_four_x0_q_jet
        boxes root_four_x0_lower root_four_x0_upper)`;;

let candle_fs_hist_reference_dihedral_real_jet_def = new_definition
 `candle_fs_hist_reference_dihedral_real_jet values =
    candle_real_hist_dihedral_jet
      (candle_fs_hist_delta_x4_real_jet values)
      (candle_fs_hist_root_delta_real_jet values)
      (candle_fs_hist_root_four_x0_real_jet values)`;;

let candle_fs_hist_reference_dihedral_q_jet_components = prove
 (`!boxes values
      delta_lower delta_upper root_delta_lower root_delta_upper
      four_x0_lower four_x0_upper root_four_x0_lower root_four_x0_upper.
     LENGTH boxes = 6 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 6) /\
     candle_fs_hist_second_value
       (candle_fs_hist_delta_second boxes) =
       ((delta_lower,0),(delta_upper,0)) /\
     0 < delta_lower /\ delta_lower <= delta_upper /\
     0 < root_delta_lower /\ root_delta_lower <= root_delta_upper /\
     &0 < candle_fs_hist_delta_real values /\
     candle_fs_interval_contains
       ((root_delta_lower,0),(root_delta_upper,0))
       (sqrt (candle_fs_hist_delta_real values)) /\
     candle_fs_hist_second_value
       (candle_fs_hist_four_x0_second boxes) =
       ((four_x0_lower,0),(four_x0_upper,0)) /\
     0 < four_x0_lower /\ four_x0_lower <= four_x0_upper /\
     0 < root_four_x0_lower /\
     root_four_x0_lower <= root_four_x0_upper /\
     &0 < candle_fs_hist_four_x0_real values /\
     candle_fs_interval_contains
       ((root_four_x0_lower,0),(root_four_x0_upper,0))
       (sqrt (candle_fs_hist_four_x0_real values)) /\
     candle_q_dim_jet_inv_domain
       (candle_q_dim_jet_normalized_mul
         (candle_fs_hist_root_delta_q_jet
           boxes root_delta_lower root_delta_upper)
         (candle_fs_hist_root_four_x0_q_jet
           boxes root_four_x0_lower root_four_x0_upper)) /\
     candle_q_dim_jet_atn_domain
       (candle_q_dim_jet_normalized_mul
         (candle_q_dim_jet_normalized_neg
           (candle_fs_hist_delta_x4_q_jet boxes))
         (candle_q_dim_jet_inv
           (candle_q_dim_jet_normalized_mul
             (candle_fs_hist_root_delta_q_jet
               boxes root_delta_lower root_delta_upper)
             (candle_fs_hist_root_four_x0_q_jet
               boxes root_four_x0_lower root_four_x0_upper))))
     ==> candle_q_dim_jet_contains_components 6
       (candle_fs_hist_reference_dihedral_q_jet boxes
         root_delta_lower root_delta_upper
         root_four_x0_lower root_four_x0_upper)
       (candle_hist_real_jet_value
         (candle_fs_hist_reference_dihedral_real_jet values))
       (candle_hist_real_jet_gradient
         (candle_fs_hist_reference_dihedral_real_jet values))
       (candle_hist_real_jet_hessian
         (candle_fs_hist_reference_dihedral_real_jet values))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_reference_dihedral_q_jet_def;
              candle_fs_hist_reference_dihedral_real_jet_def] THEN
  MATCH_MP_TAC candle_q_hist_dihedral_jet_components_sound THEN
  ASM_REWRITE_TAC[candle_fs_hist_delta_x4_q_jet_def;
                  candle_fs_hist_root_delta_q_jet_def;
                  candle_fs_hist_root_four_x0_q_jet_def;
                  candle_fs_interval_list_to_q_length;
                  candle_fs_hist_delta_x4_second_to_q_shape;
                  candle_fs_hist_root_delta_to_q_shape] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC candle_fs_hist_root_four_x0_to_q_shape THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fs_hist_delta_x4_real_jet_components THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC
      (SPECL
        [`boxes:((num#num)#(num#num))list`; `values:num->real`;
         `delta_lower:num`; `delta_upper:num`;
         `root_delta_lower:num`; `root_delta_upper:num`]
        candle_fs_hist_root_delta_real_jet_components) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC
      (SPECL
        [`boxes:((num#num)#(num#num))list`; `values:num->real`;
         `four_x0_lower:num`; `four_x0_upper:num`;
         `root_four_x0_lower:num`; `root_four_x0_upper:num`]
        candle_fs_hist_root_four_x0_real_jet_components) THEN
    ASM_REWRITE_TAC[]]);;

end;;
