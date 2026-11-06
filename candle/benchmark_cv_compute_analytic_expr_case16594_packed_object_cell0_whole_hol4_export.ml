(* ========================================================================== *)
(* Export the genuine case-16594 cell-0 four-argument whole call to HOL4.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is a bounded cross-system fixture for    *)
(* the generic witnessed callback seam.  The receiving HOL4 theory must      *)
(* authenticate the imported call and result before either can be used.      *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_registered_hol4_export.ml";;
needs "candle/test_cv_compute_analytic_expr_case16594_packed_object_cell0_whole_conditional.ml";;

module Benchmark_cv_compute_analytic_expr_case16594_packed_object_cell0_whole_hol4_export = struct

open Benchmark_cv_compute_registered_hol4_export;;
open Candle_cv_analytic_expr_packed_source_object_whole_compute;;
open Test_cv_compute_analytic_expr_case16594_packed_object_cell0_call;;
open Test_cv_compute_analytic_expr_case16594_packed_object_cell0_whole_conditional;;

let candle_case16594_object_cell0_whole_hol4_export_path =
  "/project/worktrees/cakeml-nl-packed-refinement-v1/candle/prover/compute/compute_boundedCase16594Cell0WholeHolLightDataScript.sml";;

let candle_case16594_object_cell0_whole_hol4_call =
  let dimension = DIMINDEX_CONV `dimindex (:6)` in
  let representation_rewrites =
    [dimension;
     Candle_cv_analytic_expr_packed_source_object_whole_success_sound.
       candle_cv_q_packed_object_cells_def;
     Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_sound.
       candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens_def;
     Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_sound.
       candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_token_def;
     Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch.
       candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs_def] @
    candle_case16594_object_cell0_data_rewrites in
  rand
    (concl
      (REWRITE_CONV representation_rewrites
        candle_case16594_object_cell0_whole_call));;

let candle_case16594_object_cell0_whole_hol4_result =
  rand
    (concl
      (REWRITE_CONV
        [candle_cv_q_interval_list_def;candle_cv_q_interval_def;
         candle_cv_q_def;candle_cv_lc_z_def;FST;SND]
        candle_case16594_object_cell0_whole_result));;

let _ =
  let channel = open_out candle_case16594_object_cell0_whole_hol4_export_path in
  let equations = candle_cv_q_packed_object_whole_compute_eqs () in
  candle_registered_write_data_theory channel
    "Genuine case16594 cell-0 four-argument packed-object whole call."
    "compute_boundedCase16594Cell0WholeHolLightData"
    "bounded_case16594_cell0_whole_hol_light_ceqs"
    "bounded_case16594_cell0_whole_hol_light_entry"
    "bounded_case16594_cell0_whole_hol_light_result"
    equations candle_case16594_object_cell0_whole_hol4_call
    candle_case16594_object_cell0_whole_hol4_result;
  close_out channel;
  print_endline
    ("CANDLE_CV_CASE16594_CELL0_WHOLE_HOL4_EXPORT_OK" ^
     " DEVELOPMENT_NON_RELEASE equations=" ^
     string_of_int (length equations) ^
     " path=" ^ candle_case16594_object_cell0_whole_hol4_export_path);;

end;;
