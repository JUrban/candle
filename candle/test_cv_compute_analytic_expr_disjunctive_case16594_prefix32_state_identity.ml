(* Input-identity probe without the expensive numerical computation. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_prefix32_state_fixture.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16594_prefix32_state_identity = struct

open Candle_cv_analytic_expr_jet_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_prefix32_state_fixture;;

let _ =
  let prepared,encoded =
    candle_disjunctive_case16594_prefix32_state_prepare () in
  print_endline
    ("CANDLE_CV_CASE16594_PREFIX32_STATE_IDENTITY" ^
     " encoded_md5=" ^
     candle_disjunctive_case16594_prefix32_state_term_digest encoded ^
     " source_md5=" ^
     candle_disjunctive_case16594_prefix32_state_term_digest
       prepared.program_representation_term);
  print_endline
    "CANDLE_CV_CASE16594_PREFIX32_STATE_IDENTITY_OK DEVELOPMENT_NON_RELEASE";;

end;;
