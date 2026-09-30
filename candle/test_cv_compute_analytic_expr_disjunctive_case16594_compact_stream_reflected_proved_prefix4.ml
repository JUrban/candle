(* Genuine four-cell proof through the reflected compact topology stream. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_compact_stream_prefix4_fixture.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_prove.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16594_compact_stream_reflected_proved_prefix4 = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_compact_stream_prefix4_fixture;;

let _ =
  let axioms_before = axioms () in
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE" ^
         " lane=disjunctive-case16594-reflected-proved-prefix4" ^
         " phase=" ^ event));
  let result =
    candle_q_dim_taylor_model_fixed_outer_variable_compact_reflected_source_six
      candle_disjunctive_case16594_prefix4_fixture_raw
      candle_disjunctive_case16594_prefix4_fixture_segment
      candle_disjunctive_case16594_prefix4_fixture_encoded_segment in
  let axioms_after = axioms () in
  if hyp result.variable_compact_reflected_compute_theorem <> [] ||
     hyp result.variable_compact_reflected_run_theorem <> [] ||
     hyp result.variable_compact_reflected_source_theorem <> [] ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case16594 reflected proved prefix4: validation failed";
  print_endline
    "CANDLE_CV_DISJUNCTIVE_CASE16594_REFLECTED_PROVED_PREFIX4_RESULT numerical_cells=4 token_items=7 active_roots=1 assumptions=0";
  print_endline
    "CANDLE_CV_DISJUNCTIVE_CASE16594_REFLECTED_PROVED_PREFIX4_OK DEVELOPMENT_NON_RELEASE";;

end;;
