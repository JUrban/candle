(* ========================================================================== *)
(* Export the audited fast-certificate case-16594 cell-0 call to HOL4.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This emits only data.  The receiving HOL4    *)
(* theory must prove identity with the authenticated fast entry before the    *)
(* call can be used as evidence.                                               *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_registered_hol4_export.ml";;
needs "candle/test_cv_compute_analytic_expr_case16594_packed_object_cell0_call.ml";;

module Benchmark_cv_compute_analytic_expr_case16594_packed_object_cell0_fast_hol4_export = struct

open Benchmark_cv_compute_registered_hol4_export;;
open Test_cv_compute_analytic_expr_case16594_packed_object_cell0_call;;

let candle_case16594_object_cell0_fast_hol4_export_path =
  "/project/worktrees/cakeml-nl-packed-refinement-v1/candle/prover/compute/compute_boundedCase16594Cell0FastHolLightEntryDataScript.sml";;

let _ =
  let channel = open_out candle_case16594_object_cell0_fast_hol4_export_path in
  candle_registered_write_data_theory channel
    "Audited HOL Light fast-certificate case16594 cell-0 object entry."
    "compute_boundedCase16594Cell0FastHolLightEntryData"
    "bounded_case16594_cell0_fast_hol_light_unused_ceqs"
    "bounded_case16594_cell0_fast_hol_light_entry"
    "bounded_case16594_cell0_fast_hol_light_unused_result"
    [] candle_case16594_object_cell0_call `Cexp_num 0`;
  close_out channel;
  print_endline
    ("CANDLE_CV_CASE16594_FAST_HOL4_EXPORT_OK" ^
     " DEVELOPMENT_NON_RELEASE path=" ^
     candle_case16594_object_cell0_fast_hol4_export_path);;

end;;
