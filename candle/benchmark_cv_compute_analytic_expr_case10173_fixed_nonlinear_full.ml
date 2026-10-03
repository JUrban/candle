(* ========================================================================== *)
(* Fixed nonlinear propagation on all 4,173 genuine case-10173 cells.         *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.                             *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_complete_capture.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_fixed_nonlinear_full = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear;;
open Benchmark_cv_compute_analytic_expr_case10173_complete_capture;;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE lane=case10173-fixed-nonlinear-full" ^
         " phase=" ^ event));
  let axioms_before = axioms () in
  let captured = candle_case10173_complete_capture () in
  let call =
    list_mk_comb
      (`candle_cv_fsn_variable_raw_jobs_check`,
       [captured.case10173_complete_prepared.program_representation_term;
        captured.case10173_complete_encoded_jobs]) in
  candle_q_dim_analytic_jet_profile_event "candidate-compute-begin";
  let theorem =
    candle_q_dim_analytic_jet_compute
      candle_cv_fixed_nonlinear_compute_eqs call in
  candle_q_dim_analytic_jet_profile_event "candidate-compute-end";
  let result = rand (concl theorem) in
  let axioms_after = axioms () in
  if hyp theorem <> [] || not (aconv (lhand (concl theorem)) call) ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case10173 fixed-nonlinear full: validation failed";
  print_endline
    ("CANDLE_CV_CASE10173_FIXED_NONLINEAR_FULL_OK" ^
     " DEVELOPMENT_NON_RELEASE NON_AUTHORITATIVE cells=4173 candidate_result=" ^
     (if aconv result `Cexp_num 1` then "1" else "0") ^
     " assumptions=0 axiom_growth=0");;

end;;
