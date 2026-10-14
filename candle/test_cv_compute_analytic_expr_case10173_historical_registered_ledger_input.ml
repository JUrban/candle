(* Data-only construction test for the complete case-10173 registration ledger. *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_historical_registered_ledger_input.ml";;

module Test_cv_compute_analytic_expr_case10173_historical_registered_ledger_input = struct

open Benchmark_cv_compute_analytic_expr_case10173_historical_registered_ledger_input;;

let _ =
  let axioms_before = axioms () in
  let ledger = candle_case10173_historical_registered_ledger_input () in
  let chunks = ledger.registered_ledger_chunks in
  let first = hd chunks and last = hd (rev chunks) in
  let axioms_after = axioms () in
  if length chunks <> 261 ||
     first.registered_chunk_start <> 0 ||
     first.registered_chunk_count <> 16 ||
     last.registered_chunk_start <> 4160 ||
     last.registered_chunk_count <> 13 ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case10173 registered ledger input test: validation failed";
  print_endline
    "CANDLE_CV_CASE10173_HISTORICAL_REGISTERED_LEDGER_INPUT_TEST_OK DEVELOPMENT_NON_RELEASE cells=4173 chunks=261 numerical_compute=0 axiom_growth=0";;

end;;
