(* ========================================================================== *)
(* Full-source contract for the packed analytic object entry.                 *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Final Taylor arithmetic alone is not a        *)
(* source checker: the supplied object fields must also have the proved       *)
(* analytic meaning of the authenticated source over the authenticated       *)
(* center and outer boxes.  This contract is the exact ordinary-HOL target    *)
(* for the registered fast evaluator refinement.                              *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_complete_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_entry_sound = struct

open Candle_cv_analytic_expr_packed_source_object_invariant;;
open Candle_cv_analytic_expr_packed_source_object_complete_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_object_compute;;

let candle_q_packed_source_object_accept_contract_def = new_definition
 `candle_q_packed_source_object_accept_contract
      source_boxes center_boxes outer_boxes radii domain
      center_value center_gradient value_bound gradient_bounds
      packed_hessian center_e box_e <=>
    LENGTH source_boxes = 6 /\
    candle_q_packed_source_correspondence
      source_boxes center_boxes outer_boxes radii /\
    candle_q_packed_object_item_analytic_invariant
      center_boxes outer_boxes domain center_value center_gradient
      value_bound gradient_bounds packed_hessian center_e box_e /\
    candle_cv_q_packed_object_accept6
      (candle_cv_bool domain)
      (candle_cv_q_list radii)
      (candle_cv_q_interval center_value)
      (candle_cv_q_interval_list center_gradient)
      (candle_cv_q_interval_list packed_hessian) = Cexp_num 1`;;

let candle_q_packed_source_object_accept_contract_cell_pass = prove
 (`!source_boxes center_boxes outer_boxes radii domain
       center_value center_gradient value_bound gradient_bounds
       packed_hessian center_e box_e.
     candle_q_packed_source_object_accept_contract
       source_boxes center_boxes outer_boxes radii domain
       center_value center_gradient value_bound gradient_bounds
       packed_hessian center_e box_e
     ==>
     m_cell_pass (candle_analytic_denote_dim box_e)
       ((candle_q_box_lower_vector source_boxes:real^6),
        (candle_q_box_upper_vector source_boxes:real^6))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_object_accept_contract_def] THEN
  MATCH_ACCEPT_TAC candle_cv_q_packed_object_item_accept6_cell_pass);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_source_object_accept_contract_cell_pass] then
  failwith "packed source object entry sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_ENTRY_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
