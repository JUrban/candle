(* ========================================================================== *)
(* Historical low-work dihedral: bridge the real jet to analytic syntax.    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_optimized_production_jet_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_analytic_bridge_sound = struct

open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_composition_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_production_jet_sound;;

(* Package the ordinary semantic value and its two formal derivative layers
   in the same representation used by the historical composition proof. *)

let candle_hist_analytic_real_jet_def = new_definition
 `candle_hist_analytic_real_jet env expression =
    candle_hist_real_jet_make
      (candle_analytic_value env expression)
      (\i. candle_analytic_d i env expression)
      (\i j. candle_analytic_dd i j env expression)`;;

let candle_hist_analytic_dihedral_def = new_definition
 `candle_hist_analytic_dihedral
      (delta_x4_e:candle_analytic_expr) root_delta_e root_four_x0_e =
    Candle_analytic_add Candle_analytic_pi_half
      (Candle_analytic_atn
        (Candle_analytic_mul
          (Candle_analytic_neg delta_x4_e)
          (Candle_analytic_inv
            (Candle_analytic_mul root_delta_e root_four_x0_e))))`;;

(* These are representation theorems, not calculus assumptions: the real-jet
   operators were deliberately defined by the same value/d/dd equations as
   the universal analytic language.  Keep the proof constructor-local: a
   single expansion of the complete dihedral term needlessly duplicates the
   three function-valued jet components and can exhaust the Cake heap. *)

let candle_hist_analytic_real_jet_neg = prove
 (`!env (expression:candle_analytic_expr).
     candle_hist_real_jet_neg
       (candle_hist_analytic_real_jet env expression) =
     candle_hist_analytic_real_jet env
       (Candle_analytic_neg expression)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_hist_real_jet_neg_def;
              candle_hist_analytic_real_jet_def;
              candle_hist_real_jet_make_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_hessian_def;
              candle_analytic_value_def;
              candle_analytic_d_def;
              candle_analytic_dd_def; FST; SND]);;

let candle_hist_analytic_real_jet_add = prove
 (`!env (left_expression:candle_analytic_expr) right_expression.
     candle_hist_real_jet_add
       (candle_hist_analytic_real_jet env left_expression)
       (candle_hist_analytic_real_jet env right_expression) =
     candle_hist_analytic_real_jet env
       (Candle_analytic_add left_expression right_expression)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_hist_real_jet_add_def;
              candle_hist_analytic_real_jet_def;
              candle_hist_real_jet_make_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_hessian_def;
              candle_analytic_value_def;
              candle_analytic_d_def;
              candle_analytic_dd_def; FST; SND]);;

let candle_hist_analytic_real_jet_mul = prove
 (`!env (left_expression:candle_analytic_expr) right_expression.
     candle_hist_real_jet_mul
       (candle_hist_analytic_real_jet env left_expression)
       (candle_hist_analytic_real_jet env right_expression) =
     candle_hist_analytic_real_jet env
       (Candle_analytic_mul left_expression right_expression)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_hist_real_jet_mul_def;
              candle_hist_analytic_real_jet_def;
              candle_hist_real_jet_make_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_hessian_def;
              candle_analytic_value_def;
              candle_analytic_d_def;
              candle_analytic_dd_def; FST; SND]);;

let candle_hist_analytic_real_jet_inv = prove
 (`!env (expression:candle_analytic_expr).
     candle_hist_real_jet_inv
       (candle_hist_analytic_real_jet env expression) =
     candle_hist_analytic_real_jet env
       (Candle_analytic_inv expression)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_hist_real_jet_inv_def;
              candle_hist_analytic_real_jet_def;
              candle_hist_real_jet_make_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_hessian_def;
              candle_analytic_value_def;
              candle_analytic_d_def;
              candle_analytic_dd_def; FST; SND]);;

let candle_hist_analytic_real_jet_atn = prove
 (`!env (expression:candle_analytic_expr).
     candle_hist_real_jet_atn
       (candle_hist_analytic_real_jet env expression) =
     candle_hist_analytic_real_jet env
       (Candle_analytic_atn expression)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_hist_real_jet_atn_def;
              candle_hist_analytic_real_jet_def;
              candle_hist_real_jet_make_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_hessian_def;
              candle_analytic_value_def;
              candle_analytic_d_def;
              candle_analytic_dd_def; FST; SND]);;

let candle_hist_analytic_real_jet_pi_half = prove
 (`!env.
     candle_hist_real_jet_pi_half =
     candle_hist_analytic_real_jet env Candle_analytic_pi_half`,
  GEN_TAC THEN
  REWRITE_TAC[candle_hist_real_jet_pi_half_def;
              candle_hist_analytic_real_jet_def;
              candle_hist_real_jet_make_def;
              candle_analytic_value_def;
              candle_analytic_d_def;
              candle_analytic_dd_def]);;

let candle_real_hist_dihedral_jet_is_analytic = prove
 (`!env (delta_x4_e:candle_analytic_expr) root_delta_e root_four_x0_e.
     candle_real_hist_dihedral_jet
       (candle_hist_analytic_real_jet env delta_x4_e)
       (candle_hist_analytic_real_jet env root_delta_e)
       (candle_hist_analytic_real_jet env root_four_x0_e) =
     candle_hist_analytic_real_jet env
       (candle_hist_analytic_dihedral
         delta_x4_e root_delta_e root_four_x0_e)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_real_hist_dihedral_jet_def;
              candle_hist_analytic_dihedral_def;
              candle_hist_analytic_real_jet_neg;
              candle_hist_analytic_real_jet_add;
              candle_hist_analytic_real_jet_mul;
              candle_hist_analytic_real_jet_inv;
              candle_hist_analytic_real_jet_atn;
              candle_hist_analytic_real_jet_pi_half]);;

let candle_q_hist_dihedral_components_are_analytic = prove
 (`!env (delta_x4_e:candle_analytic_expr) root_delta_e root_four_x0_e jet.
     candle_q_dim_jet_contains_components 6 jet
       (candle_hist_real_jet_value
         (candle_real_hist_dihedral_jet
           (candle_hist_analytic_real_jet env delta_x4_e)
           (candle_hist_analytic_real_jet env root_delta_e)
           (candle_hist_analytic_real_jet env root_four_x0_e)))
       (candle_hist_real_jet_gradient
         (candle_real_hist_dihedral_jet
           (candle_hist_analytic_real_jet env delta_x4_e)
           (candle_hist_analytic_real_jet env root_delta_e)
           (candle_hist_analytic_real_jet env root_four_x0_e)))
       (candle_hist_real_jet_hessian
         (candle_real_hist_dihedral_jet
           (candle_hist_analytic_real_jet env delta_x4_e)
           (candle_hist_analytic_real_jet env root_delta_e)
           (candle_hist_analytic_real_jet env root_four_x0_e)))
     ==> candle_q_dim_analytic_contains 6 jet env
       (candle_hist_analytic_dihedral
         delta_x4_e root_delta_e root_four_x0_e)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_real_hist_dihedral_jet_is_analytic;
              candle_q_dim_analytic_contains_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_hessian_def;
              candle_hist_analytic_real_jet_def;
              candle_hist_real_jet_make_def; FST; SND]);;

end;;
