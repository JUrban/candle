(* ========================================================================== *)
(* One-pass reflected whole-box Taylor arithmetic for polynomial jets.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The source expression is compiled once and   *)
(* evaluated once at the box center.  Its value, gradient, and Hessian remain *)
(* ordinary data until the final dimension-generic Taylor accumulator.        *)
(* ========================================================================== *)

needs "candle/cv_compute_polynomial_expr_dim_jet_semantics.ml";;
needs "candle/cv_compute_whole_box_dim_taylor.ml";;
needs "candle/cv_compute_whole_box_dim_taylor_sound.ml";;

module Candle_cv_polynomial_expr_dim_jet_check = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_whole_box_dim_taylor_sound;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;

let candle_q_dim_jet_taylor_upper_def = new_definition
 `candle_q_dim_jet_taylor_upper boxes jet =
    candle_q_dim_taylor_upper
      (candle_q_radius_list boxes)
      (candle_q_dim_jet_f jet)
      (candle_q_dim_jet_gradient jet)
      (candle_q_dim_jet_hessian jet)`;;

let candle_q_dim_poly_jet_whole_box_upper_def = new_definition
 `candle_q_dim_poly_jet_whole_box_upper e boxes =
    candle_q_dim_jet_taylor_upper boxes
      (candle_q_dim_jet_normalized_program
        (candle_q_center_environment_list boxes)
        (candle_poly_compile e))`;;

(* Keeping the computed jet as one call-by-value argument is intentional:   *)
(* the program traversal must not be duplicated for the three projections.  *)

let candle_cv_q_jet_upper_once_def = new_definition
 `candle_cv_q_jet_upper_once boxes jet =
    candle_cv_q_dim_taylor_upper
      (candle_cv_q_radius_list boxes)
      (Cexp_fst jet)
      (Cexp_fst (Cexp_snd jet))
      (Cexp_snd (Cexp_snd jet))`;;

let candle_cv_q_dim_poly_jet_whole_box_upper_def = new_definition
 `candle_cv_q_dim_poly_jet_whole_box_upper program boxes =
    candle_cv_q_jet_upper_once boxes
      (candle_cv_q_dim_jet_program
        (candle_cv_q_center_environment_list boxes) program)`;;

let candle_cv_q_jet_upper_once_correct = prove
 (`!boxes jet.
     candle_cv_q_jet_upper_once
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_dim_jet_encode jet) =
     candle_cv_q (candle_q_dim_jet_taylor_upper boxes jet)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_jet_upper_once_def;
              candle_q_dim_jet_taylor_upper_def;
              candle_cv_q_radius_list_correct;
              candle_cv_q_dim_jet_encode_def;
              candle_cv_q_dim_jet_make_def;
              cexp_fst_def; cexp_snd_def;
              candle_cv_q_dim_taylor_upper_correct]);;

let candle_cv_q_dim_poly_jet_whole_box_upper_correct = prove
 (`!e boxes.
     candle_cv_q_dim_poly_jet_whole_box_upper
       (candle_cv_q_instruction_list (candle_poly_compile e))
       (candle_cv_q_interval_list boxes) =
     candle_cv_q (candle_q_dim_poly_jet_whole_box_upper e boxes)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_poly_jet_whole_box_upper_def;
              candle_q_dim_poly_jet_whole_box_upper_def;
              candle_cv_q_center_environment_list_correct;
              candle_cv_q_dim_jet_program_correct;
              candle_cv_q_jet_upper_once_correct]);;

let candle_q_dim_poly_jet_whole_box_upper_source = prove
 (`!e boxes.
     candle_q_dim_poly_jet_whole_box_upper e boxes =
     candle_q_dim_jet_taylor_upper boxes
       (candle_q_dim_poly_jet_normalized
         (candle_q_center_environment_list boxes) e)`,
  REWRITE_TAC[candle_q_dim_poly_jet_whole_box_upper_def;
              candle_q_dim_poly_compile_normalized_jet_program]);;

let candle_cv_q_dim_poly_jet_whole_box_upper_sound_data = prove
 (`!e boxes.
     ?jet.
       candle_cv_q_dim_poly_jet_whole_box_upper
         (candle_cv_q_instruction_list (candle_poly_compile e))
         (candle_cv_q_interval_list boxes) =
       candle_cv_q (candle_q_dim_jet_taylor_upper boxes jet) /\
       candle_q_dim_poly_jet_contains (LENGTH boxes) jet
         (MAP (\i. candle_q_real (candle_q_midpoint i)) boxes) e`,
  REPEAT GEN_TAC THEN
  EXISTS_TAC
   `candle_q_dim_poly_jet_normalized
      (candle_q_center_environment_list boxes) e` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_cv_q_dim_poly_jet_whole_box_upper_correct;
                candle_q_dim_poly_jet_whole_box_upper_source];
    MP_TAC (SPECL
      [`e:candle_poly_expr`;
       `candle_q_center_environment_list boxes`;
       `MAP (\i. candle_q_real (candle_q_midpoint i)) boxes`]
      candle_q_dim_poly_jet_normalized_sound) THEN
    REWRITE_TAC[candle_q_center_environment_list_contains;
                candle_q_center_environment_list_length]]);;

end;;
