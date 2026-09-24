(* ========================================================================== *)
(* Shared-jet reflected whole-box Taylor arithmetic for polynomials.          *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The source expression is compiled once and    *)
(* evaluated once at the box center and once over the full box.  The center   *)
(* value/gradient and box Hessian remain ordinary data until the final        *)
(* dimension-generic Taylor accumulator.                                      *)
(* ========================================================================== *)

needs "candle/cv_compute_polynomial_expr_dim_jet_semantics.ml";;
needs "candle/cv_compute_polynomial_expr_dim_first_jet_representation.ml";;
needs "candle/cv_compute_whole_box_dim_taylor.ml";;
needs "candle/cv_compute_whole_box_dim_taylor_sound.ml";;

module Candle_cv_polynomial_expr_dim_jet_check = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_whole_box_dim_taylor_sound;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_polynomial_expr_dim_first_jet_compute;;
open Candle_cv_polynomial_expr_dim_first_jet_representation;;

let candle_q_dim_jet_taylor_upper_def = new_definition
 `candle_q_dim_jet_taylor_upper boxes center_jet box_jet =
    candle_q_dim_taylor_upper
      (candle_q_radius_list boxes)
      (candle_q_dim_jet_f center_jet)
      (candle_q_dim_jet_gradient center_jet)
      (candle_q_dim_jet_hessian box_jet)`;;

let candle_q_dim_poly_jet_whole_box_upper_def = new_definition
 `candle_q_dim_poly_jet_whole_box_upper e boxes =
    candle_q_dim_jet_taylor_upper boxes
      (candle_q_dim_jet_normalized_program
        (candle_q_center_environment_list boxes)
        (candle_poly_compile e))
      (candle_q_dim_jet_normalized_program boxes
        (candle_poly_compile e))`;;

(* Keeping each computed jet as one call-by-value argument is intentional.   *)
(* The center traversal computes only value/gradient; the full-box traversal *)
(* retains the Hessian required by the Taylor remainder.                     *)

let candle_cv_q_jet_upper_pair_def = new_definition
 `candle_cv_q_jet_upper_pair boxes center_jet box_jet =
    candle_cv_q_dim_taylor_upper
      (candle_cv_q_radius_list boxes)
      (Cexp_fst center_jet)
      (Cexp_snd center_jet)
      (Cexp_snd (Cexp_snd box_jet))`;;

let candle_cv_q_dim_poly_jet_whole_box_upper_def = new_definition
 `candle_cv_q_dim_poly_jet_whole_box_upper program boxes =
    candle_cv_q_jet_upper_pair boxes
      (candle_cv_q_dim_first_jet_program
        (candle_cv_q_center_environment_list boxes) program)
      (candle_cv_q_dim_jet_program boxes program)`;;

let candle_cv_q_jet_upper_pair_correct = prove
 (`!boxes center_jet box_jet.
     candle_cv_q_jet_upper_pair
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_dim_first_jet_encode center_jet)
       (candle_cv_q_dim_jet_encode box_jet) =
     candle_cv_q
       (candle_q_dim_jet_taylor_upper boxes center_jet box_jet)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_jet_upper_pair_def;
              candle_q_dim_jet_taylor_upper_def;
              candle_cv_q_radius_list_correct;
              candle_cv_q_dim_first_jet_encode_def;
              candle_cv_q_dim_first_jet_make_def;
              candle_cv_q_dim_jet_encode_def;
              candle_cv_q_dim_jet_make_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_def;
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
              candle_cv_q_dim_first_jet_program_correct;
              candle_cv_q_dim_jet_program_correct;
              candle_cv_q_jet_upper_pair_correct]);;

let candle_q_dim_poly_jet_whole_box_upper_source = prove
 (`!e boxes.
     candle_q_dim_poly_jet_whole_box_upper e boxes =
     candle_q_dim_jet_taylor_upper boxes
       (candle_q_dim_poly_jet_normalized
         (candle_q_center_environment_list boxes) e)
       (candle_q_dim_poly_jet_normalized boxes e)`,
  REWRITE_TAC[candle_q_dim_poly_jet_whole_box_upper_def;
              candle_q_dim_poly_compile_normalized_jet_program]);;

let candle_cv_q_dim_poly_jet_whole_box_upper_sound_data = prove
 (`!e boxes.
     ?center_jet box_jet.
       candle_cv_q_dim_poly_jet_whole_box_upper
         (candle_cv_q_instruction_list (candle_poly_compile e))
         (candle_cv_q_interval_list boxes) =
       candle_cv_q
         (candle_q_dim_jet_taylor_upper boxes center_jet box_jet) /\
       candle_q_dim_poly_jet_contains (LENGTH boxes) center_jet
         (MAP (\i. candle_q_real (candle_q_midpoint i)) boxes) e /\
       (!env. candle_q_stack_contains boxes env
              ==> candle_q_dim_poly_jet_contains (LENGTH boxes)
                    box_jet env e)`,
  REPEAT GEN_TAC THEN
  EXISTS_TAC
   `candle_q_dim_poly_jet_normalized
      (candle_q_center_environment_list boxes) e` THEN
  EXISTS_TAC `candle_q_dim_poly_jet_normalized boxes e` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_cv_q_dim_poly_jet_whole_box_upper_correct;
                candle_q_dim_poly_jet_whole_box_upper_source];
    MP_TAC (SPECL
      [`e:candle_poly_expr`;
       `candle_q_center_environment_list boxes`;
       `MAP (\i. candle_q_real (candle_q_midpoint i)) boxes`]
      candle_q_dim_poly_jet_normalized_sound) THEN
    REWRITE_TAC[candle_q_center_environment_list_contains;
                candle_q_center_environment_list_length] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC candle_q_dim_poly_jet_normalized_sound THEN
      ASM_REWRITE_TAC[]]]);;

(* The reflected checker deliberately treats source validity separately.     *)
(* The source reifier proves that once for the expression; the recurring     *)
(* numerical check validates the box and the sign of the computed bound.     *)

let candle_q_dim_poly_jet_whole_box_numerical_accept_def = new_definition
 `candle_q_dim_poly_jet_whole_box_numerical_accept e boxes <=>
    candle_q_box_valid_list boxes /\
    ~(candle_q_le candle_q_zero
       (candle_q_dim_poly_jet_whole_box_upper e boxes))`;;

let candle_cv_q_dim_poly_jet_whole_box_check_def = new_definition
 `candle_cv_q_dim_poly_jet_whole_box_check program boxes =
    candle_cv_q_dim_whole_box_finish
      (Cexp_num (SUC 0))
      (candle_cv_q_box_valid_list boxes)
      (candle_cv_q_dim_poly_jet_whole_box_upper program boxes)`;;

let candle_cv_q_dim_poly_jet_whole_box_check_correct = prove
 (`!e boxes.
     candle_cv_q_dim_poly_jet_whole_box_check
       (candle_cv_q_instruction_list (candle_poly_compile e))
       (candle_cv_q_interval_list boxes) =
     Cexp_pair
       (Cexp_num
         (if candle_q_dim_poly_jet_whole_box_numerical_accept e boxes
          then SUC 0 else 0))
       (candle_cv_q (candle_q_dim_poly_jet_whole_box_upper e boxes))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_poly_jet_whole_box_check_def;
              candle_cv_q_box_valid_list_correct;
              candle_cv_q_dim_poly_jet_whole_box_upper_correct;
              candle_q_dim_poly_jet_whole_box_numerical_accept_def] THEN
  let finish_th =
    SPECL
     [`T`;
      `candle_q_box_valid_list
        (boxes:(((num#num)#num)#((num#num)#num))list)`;
     `candle_q_dim_poly_jet_whole_box_upper e boxes`]
     candle_cv_q_dim_whole_box_finish_correct in
  ACCEPT_TAC (REWRITE_RULE[] finish_th));;

end;;
