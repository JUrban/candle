(* ========================================================================== *)
(* Logical representation and invariant for fixed nonlinear tagged items.    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_invariant.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_compile_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_item_invariant = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_analytic_dim_jet_pi_half;;
open Candle_cv_analytic_expr_fixed_scale_compute;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_fixed_scale_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_item_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_program_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compile_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_invariant;;

let candle_fsn_item_accept label (th:thm) : tactic =
  fun (assumptions,goal) ->
    try MATCH_ACCEPT_TAC th (assumptions,goal) with Failure _ ->
      print_endline (label ^ " expected:");
      print_term goal; print_newline ();
      print_endline (label ^ " theorem:");
      print_term (concl th); print_newline ();
      failwith label;;

let candle_fsn_logical_item_of_result_def = new_definition
 `candle_fsn_logical_item_of_result
      (result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list) =
    candle_fsa_logical_item_make T result (candle_fs_result_to_q result)`;;

let candle_fsn_logical_item_inv_def = new_definition
 `candle_fsn_logical_item_inv radii item =
    candle_fsn_logical_item_of_result
      (candle_fsn_result_inv (candle_fs_list_of_q radii)
        (candle_fsa_item_fixed_view
          (candle_fsa_logical_item_tag item)
          (candle_fsa_logical_item_fixed item)
          (candle_fsa_logical_item_q item)))`;;

let candle_fsn_logical_item_sqrt_def = new_definition
 `candle_fsn_logical_item_sqrt radii center_certificate box_certificate item =
    candle_fsn_logical_item_of_result
      (candle_fsn_result_sqrt (candle_fs_list_of_q radii)
        center_certificate box_certificate
        (candle_fsa_item_fixed_view
          (candle_fsa_logical_item_tag item)
          (candle_fsa_logical_item_fixed item)
          (candle_fsa_logical_item_q item)))`;;

let candle_fsn_logical_item_atn_def = new_definition
 `candle_fsn_logical_item_atn radii item =
    candle_fsn_logical_item_of_result
      (candle_fsn_result_atn (candle_fs_list_of_q radii)
        (candle_fsa_item_fixed_view
          (candle_fsa_logical_item_tag item)
          (candle_fsa_logical_item_fixed item)
          (candle_fsa_logical_item_q item)))`;;

(* [pi_half] only consumes the length of its dimension argument.  The live
   program supplies the encoded rational box list, whereas the older generic
   result theorem happened to state that shape fact over a fixed-interval
   encoding.  These lemmas authenticate the rational-list route directly. *)

let candle_cv_fs_interval_zeros_q_dimensions_correct = prove
 (`!items.
     candle_cv_fs_interval_zeros (candle_cv_q_interval_list items) =
     candle_cv_fs_interval_list
       (candle_fs_interval_zeros (candle_fs_interval_list_of_q items))`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_q_interval_list_def;
                  candle_cv_fs_interval_zeros_def;
                  candle_cv_fs_interval_list_def;
                  candle_fs_interval_list_of_q_def;
                  candle_fs_interval_zeros_def;
                  candle_cv_fs_interval_zero_correct]);;

let candle_cv_fs_interval_zero_matrix_q_dimensions_correct = prove
 (`!width dimensions.
     candle_cv_fs_interval_zero_matrix
       (candle_cv_q_interval_list width)
       (candle_cv_q_interval_list dimensions) =
     candle_cv_fs_interval_matrix
       (candle_fs_interval_zero_matrix
         (candle_fs_interval_list_of_q width)
         (candle_fs_interval_list_of_q dimensions))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_q_interval_list_def;
                  candle_cv_fs_interval_zero_matrix_def;
                  candle_cv_fs_interval_matrix_def;
                  candle_fs_interval_list_of_q_def;
                  candle_fs_interval_zero_matrix_def;
                  candle_cv_fs_interval_zeros_q_dimensions_correct]);;

let candle_cv_fsn_result_pi_half_q_dimensions_correct = prove
 (`!radii dimensions.
     candle_cv_fsn_result_pi_half
       (candle_cv_lc_vec radii)
       (candle_cv_q_interval_list dimensions) =
     candle_cv_fs_result
       (candle_fsn_result_pi_half radii
         (candle_fs_interval_list_of_q dimensions))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsn_result_pi_half_def;
              candle_fsn_result_pi_half_def;
              candle_cv_q_pi_half_interval_correct;
              candle_cv_fs_interval_of_q_correct;
              candle_cv_fs_interval_zeros_q_dimensions_correct;
              candle_cv_fs_first_make_correct;
              candle_cv_fs_interval_zero_matrix_q_dimensions_correct;
              candle_cv_fs_result_complete_true_correct]);;

let candle_fsn_logical_item_pi_half_def = new_definition
 `candle_fsn_logical_item_pi_half radii dimensions =
    candle_fsn_logical_item_of_result
      (candle_fsn_result_pi_half (candle_fs_list_of_q radii)
        (candle_fs_interval_list_of_q dimensions))`;;

let candle_cv_fsn_logical_item_inv_correct = prove
 (`!radii item.
     candle_cv_fsn_item_inv (candle_cv_q_list radii)
       (candle_cv_fsa_logical_item_encode item) =
     candle_cv_fsa_logical_item_encode
       (candle_fsn_logical_item_inv radii item)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsn_item_inv_def;
              candle_fsn_logical_item_inv_def;
              candle_fsn_logical_item_of_result_def;
              candle_cv_fsa_logical_item_encode_def;
              candle_fsa_logical_item_make_def;
              candle_fsa_logical_item_tag_def;
              candle_fsa_logical_item_fixed_def;
              candle_fsa_logical_item_q_def] THEN
  REWRITE_TAC[candle_cv_fsa_item_to_fixed_correct;
              candle_cv_fs_list_of_q_correct;
              candle_cv_fsn_result_inv_correct] THEN
  REWRITE_TAC[
              candle_cv_fsa_item_encode_def;
              candle_cv_fsa_item_fixed_def]);;

let candle_cv_fsn_logical_item_sqrt_correct = prove
 (`!radii center_certificate box_certificate item.
     candle_cv_fsn_item_sqrt (candle_cv_q_list radii)
       (candle_cv_q_interval center_certificate)
       (candle_cv_q_interval box_certificate)
       (candle_cv_fsa_logical_item_encode item) =
     candle_cv_fsa_logical_item_encode
       (candle_fsn_logical_item_sqrt radii
         center_certificate box_certificate item)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsn_item_sqrt_def;
              candle_fsn_logical_item_sqrt_def;
              candle_fsn_logical_item_of_result_def;
              candle_cv_fsa_logical_item_encode_def;
              candle_fsa_logical_item_make_def;
              candle_fsa_logical_item_tag_def;
              candle_fsa_logical_item_fixed_def;
              candle_fsa_logical_item_q_def] THEN
  REWRITE_TAC[candle_cv_fsa_item_to_fixed_correct;
              candle_cv_fs_list_of_q_correct;
              candle_cv_fsn_result_sqrt_correct] THEN
  REWRITE_TAC[
              candle_cv_fsa_item_encode_def;
              candle_cv_fsa_item_fixed_def]);;

let candle_cv_fsn_logical_item_atn_correct = prove
 (`!radii item.
     candle_cv_fsn_item_atn (candle_cv_q_list radii)
       (candle_cv_fsa_logical_item_encode item) =
     candle_cv_fsa_logical_item_encode
       (candle_fsn_logical_item_atn radii item)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsn_item_atn_def;
              candle_fsn_logical_item_atn_def;
              candle_fsn_logical_item_of_result_def;
              candle_cv_fsa_logical_item_encode_def;
              candle_fsa_logical_item_make_def;
              candle_fsa_logical_item_tag_def;
              candle_fsa_logical_item_fixed_def;
              candle_fsa_logical_item_q_def] THEN
  REWRITE_TAC[candle_cv_fsa_item_to_fixed_correct;
              candle_cv_fs_list_of_q_correct;
              candle_cv_fsn_result_atn_correct] THEN
  REWRITE_TAC[
              candle_cv_fsa_item_encode_def;
              candle_cv_fsa_item_fixed_def]);;

let candle_cv_fsn_logical_item_pi_half_correct = prove
 (`!radii dimensions.
     candle_cv_fsn_item_pi_half (candle_cv_q_list radii)
       (candle_cv_q_interval_list dimensions) =
     candle_cv_fsa_logical_item_encode
       (candle_fsn_logical_item_pi_half radii dimensions)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsn_item_pi_half_def;
              candle_fsn_logical_item_pi_half_def;
              candle_fsn_logical_item_of_result_def;
              candle_cv_fsa_logical_item_encode_def;
              candle_fsa_logical_item_make_def;
              candle_fsa_logical_item_tag_def;
              candle_fsa_logical_item_fixed_def;
              candle_fsa_logical_item_q_def] THEN
  REWRITE_TAC[
              candle_cv_fs_list_of_q_correct;
              candle_cv_fsn_result_pi_half_q_dimensions_correct] THEN
  REWRITE_TAC[
              candle_cv_fsa_item_encode_def;
              candle_cv_fsa_item_fixed_def]);;

let candle_fsn_logical_item_inv_analytic_invariant = prove
 (`!center_e box_e boxes item (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_fsa_logical_item_analytic_invariant
       type_witness boxes item center_e box_e
     ==>
     candle_fsa_logical_item_analytic_invariant type_witness boxes
       (candle_fsn_logical_item_inv
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes)) item)
       (Candle_analytic_inv center_e) (Candle_analytic_inv box_e)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsa_logical_item_analytic_invariant_def;
              candle_fsn_logical_item_inv_def;
              candle_fsn_logical_item_of_result_def;
              candle_fsa_logical_item_make_def;
              candle_fsa_logical_item_tag_def;
              candle_fsa_logical_item_fixed_def;
              candle_fsa_logical_item_q_def] THEN
  candle_fsn_item_accept "fixed nonlinear logical inv invariant"
    (REWRITE_RULE[LET_DEF; LET_END_DEF]
      candle_fsn_item_inv_analytic_invariant));;

let candle_fsn_logical_item_sqrt_analytic_invariant = prove
 (`!clp cln cld cup cun cud blp bln bld bup bun bud
      center_e box_e boxes item (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_fsa_logical_item_analytic_invariant
       type_witness boxes item center_e box_e
     ==>
     candle_fsa_logical_item_analytic_invariant type_witness boxes
       (candle_fsn_logical_item_sqrt
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_analytic_sqrt_interval clp cln cld cup cun cud)
         (candle_analytic_sqrt_interval blp bln bld bup bun bud) item)
       (Candle_analytic_sqrt clp cln cld cup cun cud center_e)
       (Candle_analytic_sqrt blp bln bld bup bun bud box_e)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsa_logical_item_analytic_invariant_def;
              candle_fsn_logical_item_sqrt_def;
              candle_fsn_logical_item_of_result_def;
              candle_fsa_logical_item_make_def;
              candle_fsa_logical_item_tag_def;
              candle_fsa_logical_item_fixed_def;
              candle_fsa_logical_item_q_def] THEN
  candle_fsn_item_accept "fixed nonlinear logical sqrt invariant"
    (REWRITE_RULE[LET_DEF; LET_END_DEF]
      candle_fsn_item_sqrt_analytic_invariant));;

let candle_fsn_logical_item_atn_analytic_invariant = prove
 (`!center_e box_e boxes item (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_fsa_logical_item_analytic_invariant
       type_witness boxes item center_e box_e
     ==>
     candle_fsa_logical_item_analytic_invariant type_witness boxes
       (candle_fsn_logical_item_atn
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes)) item)
       (Candle_analytic_atn center_e) (Candle_analytic_atn box_e)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsa_logical_item_analytic_invariant_def;
              candle_fsn_logical_item_atn_def;
              candle_fsn_logical_item_of_result_def;
              candle_fsa_logical_item_make_def;
              candle_fsa_logical_item_tag_def;
              candle_fsa_logical_item_fixed_def;
              candle_fsa_logical_item_q_def] THEN
  candle_fsn_item_accept "fixed nonlinear logical atn invariant"
    (REWRITE_RULE[LET_DEF; LET_END_DEF]
      candle_fsn_item_atn_analytic_invariant));;

let candle_fsn_logical_item_pi_half_analytic_invariant = prove
 (`!boxes dimensions (type_witness:real^N).
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     LENGTH dimensions = dimindex (:N)
     ==>
     candle_fsa_logical_item_analytic_invariant type_witness boxes
       (candle_fsn_logical_item_pi_half
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         dimensions)
       Candle_analytic_pi_half Candle_analytic_pi_half`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fsa_logical_item_analytic_invariant_def;
              candle_fsn_logical_item_pi_half_def;
              candle_fsn_logical_item_of_result_def;
              candle_fsa_logical_item_make_def;
              candle_fsa_logical_item_tag_def;
              candle_fsa_logical_item_fixed_def;
              candle_fsa_logical_item_q_def;
              candle_fs_interval_list_of_q_length] THEN
  MATCH_MP_TAC
    (REWRITE_RULE[LET_DEF; LET_END_DEF]
      candle_fsn_item_pi_half_analytic_invariant) THEN
  ASM_REWRITE_TAC[candle_fs_interval_list_of_q_length]);;

end;;
