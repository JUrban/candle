(* ========================================================================== *)
(* Export a genuinely bounded 16-cell prefix before HOL4 translation.        *)
(*                                                                            *)
(* Unlike slicing the generated HOL4 constant, this constructs the prefix in *)
(* HOL Light and writes only those job/root records.  It therefore measures  *)
(* bounded registration rather than translation of the complete 4,173-cell  *)
(* expression followed by a late slice.                                      *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_historical_registered_full_capture.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_historical_registered_chunk16_export = struct

open Benchmark_cv_compute_registered_hol4_export;;
open Benchmark_cv_compute_analytic_expr_case10173_historical_registered_full_capture;;

let rec candle_registered_cval_list_take count encoded =
  if count = 0 then `Cexp_num 0`
  else
    let operator,arguments = strip_comb encoded in
    let name,_ = dest_const operator in
    match name,arguments with
    | "Cexp_pair",[head;tail] ->
        list_mk_comb
          (`Cexp_pair`,
           [head;candle_registered_cval_list_take (count - 1) tail])
    | _ -> failwith "registered chunk export: short or malformed cval list";;

let candle_case10173_historical_registered_chunk16_export_path =
  "/project/flyspeck-candle-runs/nl-case10173-registered-chunk16-generated-v1.sml";;

let _ =
  let equations,full_call,_ =
    candle_case10173_historical_registered_full_capture () in
  let operator,arguments = strip_comb full_call in
  let source_program,encoded_jobs,roots =
    match arguments with
    | [source_program;encoded_jobs;roots] ->
        source_program,encoded_jobs,roots
    | _ -> failwith "registered chunk export: malformed full call" in
  let chunk_call =
    list_mk_comb
      (operator,
       [source_program;
        candle_registered_cval_list_take 16 encoded_jobs;
        candle_registered_cval_list_take 16 roots]) in
  let channel =
    open_out candle_case10173_historical_registered_chunk16_export_path in
  candle_registered_write_data_theory channel
    "Mechanically exported genuine 16-cell case-10173 checked-call prefix."
    "compute_registeredCase10173HistoricalChunk16Data"
    "registered_case10173_historical_chunk16_ceqs"
    "registered_case10173_historical_chunk16_cexp"
    "registered_case10173_historical_chunk16_result"
    equations
    chunk_call
    `Cexp_num 1`;
  close_out channel;
  print_endline
    ("CANDLE_CV_CASE10173_HISTORICAL_REGISTERED_CHUNK16_EXPORT_OK" ^
     " DEVELOPMENT_NON_RELEASE cells=16 equations=" ^
     string_of_int (length equations) ^
     " path=" ^ candle_case10173_historical_registered_chunk16_export_path);;

end;;
