(* ========================================================================== *)
(* Export the complete aligned exact-registration ledger for case 10173.     *)
(*                                                                            *)
(* The authenticated 4,173-job call is split before HOL4 rendering.  Every   *)
(* full chunk contains 16 jobs and aligned root records; the final chunk      *)
(* contains 13.  This is a temporary first-inequality fallback while the      *)
(* reusable packed word/object refinement is completed.                       *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_historical_registered_chunk_export.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_historical_registered_ledger_export = struct

open Benchmark_cv_compute_analytic_expr_case10173_historical_registered_chunk_export;;

let candle_case10173_historical_registered_ledger_output_dir =
  "/project/flyspeck-candle-runs/nl-case10173-registered-ledger-v1-generated";;

let candle_case10173_historical_registered_ledger_chunk_size = 16;;
let candle_case10173_historical_registered_ledger_cell_count = 4173;;

let candle_case10173_historical_registered_ledger_data_name start count =
  "compute_registeredCase10173HistoricalChunkAt" ^ string_of_int start ^
  "Count" ^ string_of_int count ^ "DataScript.sml";;

let rec candle_case10173_historical_registered_export_ledger start chunks =
  if start = candle_case10173_historical_registered_ledger_cell_count then
    chunks
  else
    let count =
      min candle_case10173_historical_registered_ledger_chunk_size
        (candle_case10173_historical_registered_ledger_cell_count - start) in
    let path =
      candle_case10173_historical_registered_ledger_output_dir ^ "/" ^
      candle_case10173_historical_registered_ledger_data_name start count in
    candle_case10173_historical_registered_export_chunk start count path;
    candle_case10173_historical_registered_export_ledger
      (start + count) (chunks + 1);;

let candle_case10173_historical_registered_ledger_chunks =
  candle_case10173_historical_registered_export_ledger 0 0;;

if candle_case10173_historical_registered_ledger_chunks <> 261 then
  failwith "case10173 registered ledger export: chunk-count drift";;

print_endline
  ("CANDLE_CV_CASE10173_HISTORICAL_REGISTERED_LEDGER_EXPORT_OK" ^
   " DEVELOPMENT_NON_RELEASE cells=4173 chunks=" ^
   string_of_int candle_case10173_historical_registered_ledger_chunks ^
   " chunk_size=16 final_chunk=13");;

end;;
