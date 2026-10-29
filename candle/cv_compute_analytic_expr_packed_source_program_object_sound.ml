(* ========================================================================== *)
(* Whole-program source replay to the packed analytic-object invariant.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Two successful authenticated source replays  *)
(* produce the center and outer items, and the packed Hessian is tied to the  *)
(* outer result.  Final Taylor acceptance is deliberately left to the         *)
(* separately proved source-object entry contract.                            *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_merge_sound.ml";;

module Candle_cv_analytic_expr_packed_source_program_object_sound = struct

open Candle_cv_analytic_expr_packed_source_step_sound;;
open Candle_cv_analytic_expr_packed_source_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_merge_sound;;

let candle_q_packed_source_program_run_empty_analytic_invariant = prove
 (`!boxes sources result.
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     candle_q_packed_source_program_run boxes sources [] result
     ==>
     candle_q_packed_source_stack_analytic_invariant boxes result`,
  MESON_TAC[candle_q_packed_source_program_run_analytic_invariant;
            candle_q_packed_source_stack_analytic_invariant_def]);;

let candle_q_packed_source_programs_object_invariant = prove
 (`!center_boxes outer_boxes center_sources outer_sources
       center_item outer_item packed_hessian.
     LENGTH center_boxes = 6 /\
     LENGTH outer_boxes = 6 /\
     candle_q_box_valid_list center_boxes /\
     candle_q_box_valid_list outer_boxes /\
     candle_q_packed_source_program_run
       center_boxes center_sources [] (CONS center_item []) /\
     candle_q_packed_source_program_run
       outer_boxes outer_sources [] (CONS outer_item []) /\
     candle_analytic_erase_sqrt_certificates
       (candle_q_packed_source_item_box_expr center_item) =
       candle_analytic_erase_sqrt_certificates
         (candle_q_packed_source_item_box_expr outer_item) /\
     candle_q_packed_hessian6_expand packed_hessian =
       candle_q_dim_taylor_model_result_hessian
         (candle_q_packed_source_item_result outer_item)
     ==>
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes
       (candle_q_dim_taylor_model_result_domain
          (candle_q_packed_source_item_result center_item) /\
        candle_q_dim_taylor_model_result_domain
          (candle_q_packed_source_item_result outer_item))
       (candle_q_dim_taylor_model_result_value_bound
         (candle_q_packed_source_item_result center_item))
       (candle_q_dim_taylor_model_result_gradient_bounds
         (candle_q_packed_source_item_result center_item))
       (candle_q_dim_taylor_model_result_value_bound
         (candle_q_packed_source_item_result outer_item))
       (candle_q_dim_taylor_model_result_gradient_bounds
         (candle_q_packed_source_item_result outer_item))
       packed_hessian
       (candle_q_packed_source_item_box_expr center_item)
       (candle_q_packed_source_item_box_expr outer_item)`,
  MESON_TAC
    [candle_q_packed_source_program_run_empty_analytic_invariant;
     candle_q_packed_source_stack_analytic_invariant_def;
     candle_q_packed_source_items_merge_object_invariant]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_source_program_run_empty_analytic_invariant;
     candle_q_packed_source_programs_object_invariant] then
  failwith "packed source program object sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_PROGRAM_OBJECT_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
