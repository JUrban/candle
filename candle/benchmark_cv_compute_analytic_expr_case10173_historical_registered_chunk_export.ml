(* ========================================================================== *)
(* Export an indexed genuine case-10173 checked-call chunk for HOL4.          *)
(*                                                                            *)
(* The complete authenticated capture contains aligned job and root lists.   *)
(* Slice both lists before rendering so HOL4 registration cost is bounded by *)
(* the requested chunk rather than the complete 4,173-cell term.             *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_historical_registered_full_capture.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_historical_registered_chunk_export = struct

open Benchmark_cv_compute_registered_hol4_export;;
open Benchmark_cv_compute_analytic_expr_case10173_historical_registered_full_capture;;

let candle_registered_cval_list_view encoded =
  let operator,arguments = strip_comb encoded in
  let name,_ = dest_const operator in
  match name,arguments with
  | "Cexp_num",[zero] when dest_numeral zero =/ Num.num_of_int 0 -> None
  | "Cexp_pair",[head;tail] -> Some (head,tail)
  | _ -> failwith "registered chunk export: malformed cval list";;

let rec candle_registered_cval_list_length encoded =
  match candle_registered_cval_list_view encoded with
  | None -> 0
  | Some (_,tail) -> 1 + candle_registered_cval_list_length tail;;

let rec candle_registered_cval_list_drop count encoded =
  if count = 0 then encoded
  else
    match candle_registered_cval_list_view encoded with
    | Some (_,tail) -> candle_registered_cval_list_drop (count - 1) tail
    | None -> failwith "registered chunk export: drop exceeds cval list";;

let rec candle_registered_cval_list_take count encoded =
  if count = 0 then `Cexp_num 0`
  else
    match candle_registered_cval_list_view encoded with
    | Some (head,tail) ->
        list_mk_comb
          (`Cexp_pair`,
           [head;candle_registered_cval_list_take (count - 1) tail])
    | None -> failwith "registered chunk export: take exceeds cval list";;

let candle_registered_cval_list_slice start count encoded =
  candle_registered_cval_list_take count
    (candle_registered_cval_list_drop start encoded);;

let candle_case10173_historical_registered_export_chunk start count path =
  let total = 4173 in
  if start < 0 || count <= 0 || start > total || count > total - start then
    failwith "registered chunk export: invalid half-open cell range";
  let equations,full_call,_ =
    candle_case10173_historical_registered_full_capture () in
  let operator,arguments = strip_comb full_call in
  let source_program,encoded_jobs,roots =
    match arguments with
    | [source_program;encoded_jobs;roots] ->
        source_program,encoded_jobs,roots
    | _ -> failwith "registered chunk export: malformed full call" in
  let job_count = candle_registered_cval_list_length encoded_jobs in
  let root_count = candle_registered_cval_list_length roots in
  if job_count <> total || root_count <> total then
    failwith "registered chunk export: complete aligned-list length drift";
  let encoded_jobs_chunk =
    candle_registered_cval_list_slice start count encoded_jobs in
  let roots_chunk = candle_registered_cval_list_slice start count roots in
  let chunk_call =
    list_mk_comb
      (operator,[source_program;encoded_jobs_chunk;roots_chunk]) in
  let suffix = "At" ^ string_of_int start ^ "Count" ^ string_of_int count in
  let identifier_suffix =
    "at" ^ string_of_int start ^ "_count" ^ string_of_int count in
  let channel = open_out path in
  candle_registered_write_data_theory channel
    ("Mechanically exported genuine case-10173 checked-call cells [" ^
     string_of_int start ^ "," ^ string_of_int (start + count) ^ ").")
    ("compute_registeredCase10173HistoricalChunk" ^ suffix ^ "Data")
    ("registered_case10173_historical_chunk_" ^ identifier_suffix ^ "_ceqs")
    ("registered_case10173_historical_chunk_" ^ identifier_suffix ^ "_cexp")
    ("registered_case10173_historical_chunk_" ^ identifier_suffix ^ "_result")
    equations chunk_call `Cexp_num 1`;
  close_out channel;
  print_endline
    ("CANDLE_CV_CASE10173_HISTORICAL_REGISTERED_CHUNK_EXPORT_OK" ^
     " DEVELOPMENT_NON_RELEASE start=" ^ string_of_int start ^
     " count=" ^ string_of_int count ^
     " end=" ^ string_of_int (start + count) ^
     " total=" ^ string_of_int total ^
     " equations=" ^ string_of_int (length equations) ^
     " path=" ^ path);;

end;;
