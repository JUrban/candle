(* ========================================================================== *)
(* Export exact genuine case-10173 certificate boxes for native diagnostics. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.  This emits ordinary text  *)
(* data only.  It proves no bound and contributes no theorem evidence.        *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_variable_raw_plan.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_export_boxes = struct

open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Benchmark_cv_compute_analytic_expr_case10173_variable_raw_plan;;

let candle_case10173_export_rational term =
  Num.string_of_num (rat_of_term term);;

let candle_case10173_export_vector terms =
  String.concat "," (map candle_case10173_export_rational terms);;

let rec candle_case10173_export_rows index rows = function
  | [] -> rev rows
  | cell :: remaining ->
      let stable = cell.variable_batch_stable_cell in
      if length stable.stable_batch_lower <> 6 ||
         length stable.stable_batch_upper <> 6 then
        failwith "case10173 box export: dimension drift";
      let row =
        string_of_int index ^ "\t" ^
        candle_case10173_export_vector stable.stable_batch_lower ^ "\t" ^
        candle_case10173_export_vector stable.stable_batch_upper in
      candle_case10173_export_rows (index + 1) (row :: rows) remaining;;

let _ =
  let axioms_before = axioms () in
  let plan = candle_case10173_variable_raw_plan () in
  let rows =
    candle_case10173_export_rows 0 []
      plan.case10173_variable_raw_plan_cells in
  if length rows <> 4173 then
    failwith "case10173 box export: cell count drift";
  let payload = String.concat "\n" rows ^ "\n" in
  let digest = Digest.to_hex (Digest.string payload) in
  List.iter
    (fun row -> print_endline ("CANDLE_CV_NL_BOX\t10173\t" ^ row))
    rows;
  let axioms_after = axioms () in
  if length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case10173 box export: axiom-set drift";
  print_endline
    ("CANDLE_CV_CASE10173_BOX_EXPORT_OK DEVELOPMENT_NON_RELEASE" ^
     " boxes=4173 dimensions=6 payload_md5=" ^ digest ^
     " assumptions=0 axiom_growth=0");;

end;;
