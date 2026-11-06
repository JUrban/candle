(* ========================================================================== *)
(* Exact-object dispatch call for genuine case-16594 cell 0.                *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The fixture is untrusted data.  This module  *)
(* only constructs and audits the closed executable call; acceptance must be *)
(* produced by the verified evaluator and consumed by the generic soundness  *)
(* theorem.                                                                   *)
(* ========================================================================== *)

needs "candle/test_cv_compute_analytic_expr_case16594_packed_cell0_plan.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_dispatch_entry_success_sound.ml";;

module Test_cv_compute_analytic_expr_case16594_packed_object_cell0_call = struct

open Candle_cv_analytic_expr_packed_source_object_dispatch_compute;;
open Candle_cv_analytic_expr_packed_source_object_dispatch_entry;;
open Candle_cv_analytic_expr_packed_source_object_dispatch_entry_success_sound;;
open Test_cv_compute_analytic_expr_case16594_packed_cell0_correspondence;;
open Test_cv_compute_analytic_expr_case16594_packed_cell0_entry_fixture;;
open Test_cv_compute_analytic_expr_case16594_packed_cell0_plan;;

let candle_case16594_object_cell0_logical_call =
  list_mk_comb
    (`candle_cv_q_packed_object_dispatch_entry`,
     [mk_comb
        (`candle_cv_q_interval_list`,
         candle_case16594_cell0_center_boxes);
      mk_comb
        (`candle_cv_q_interval_list`,
         candle_case16594_cell0_outer_boxes);
      mk_comb (`candle_cv_q_list`,candle_case16594_cell0_radii);
      mk_comb
        (`candle_cv_q_packed_object_plan_code_list`,
         candle_case16594_cell0_plan_codes);
      mk_comb
        (`candle_cv_analytic_instruction_list`,
         candle_case16594_cell0_sources);
      mk_comb
        (`candle_cv_q_interval_list`,
         candle_case16594_cell0_certificates)]);;

let candle_case16594_object_cell0_data_rewrites =
  [candle_cv_q_packed_object_plan_code_list_def;
   Candle_cv_analytic_expr_program_compute.
     candle_cv_analytic_instruction_list_def;
   Candle_cv_analytic_expr_program_compute.candle_cv_analytic_instruction_def;
   Candle_cv_exact_interval_program.candle_cv_q_instruction_list_def;
   Candle_cv_exact_interval_program.candle_cv_q_instruction_def;
   Candle_cv_analytic_expr_jet.candle_analytic_sqrt_interval_def;
   Candle_cv_exact_interval_program.candle_cv_q_interval_list_def;
   Candle_cv_exact_interval_core.candle_cv_q_interval_def;
   Candle_cv_whole_box_dim_taylor.candle_cv_q_list_def;
   Candle_cv_exact_rational_core.candle_cv_q_def;
   Candle_cv_linear_combination_core.candle_cv_lc_z_def;
   FST; SND];;

let candle_case16594_object_cell0_representation =
  REWRITE_CONV candle_case16594_object_cell0_data_rewrites
    candle_case16594_object_cell0_logical_call;;

let candle_case16594_object_cell0_call =
  rand (concl candle_case16594_object_cell0_representation);;

let _ =
  let operator,arguments =
    strip_comb candle_case16594_object_cell0_call in
  if hyp candle_case16594_object_cell0_representation <> [] ||
     not (aconv operator `candle_cv_q_packed_object_dispatch_entry`) ||
     length arguments <> 6 ||
     length (dest_list candle_case16594_cell0_sources) <> 167 ||
     length (dest_list candle_case16594_cell0_plan_codes) <> 167 ||
     length (dest_list candle_case16594_cell0_certificates) <> 134 ||
     hyp candle_case16594_cell0_plan <> [] then
    failwith "case16594 object cell0: closed call audit failed";;

print_endline
  "CANDLE_CV_CASE16594_PACKED_OBJECT_CELL0_CALL_OK instructions=167 certificates=134 assumptions=0 DEVELOPMENT_NON_RELEASE";;

end;;
