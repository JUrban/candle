(* ========================================================================== *)
(* Export the exact complete case-16594 inputs for native discriminators.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.  The source program,      *)
(* square-root certificates, centers, and boxes are ordinary diagnostic      *)
(* data.  This fragment creates no numerical verdict or theorem evidence.    *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_complete_full_precomputed_capture.ml";;

module Benchmark_cv_compute_analytic_expr_case16594_native_inputs_full = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_complete_full_precomputed_capture;;

let candle_case16594_native_input_rational term =
  Num.string_of_num (rat_of_term term);;

let candle_case16594_native_input_vector terms =
  String.concat "," (map candle_case16594_native_input_rational terms);;

let candle_case16594_native_input_q_data term =
  let signed,denominator_predecessor = dest_pair term in
  let positive,negative = dest_pair signed in
  let numerator =
    Num.sub_num (dest_numeral positive) (dest_numeral negative) in
  let denominator =
    Num.add_num (dest_numeral denominator_predecessor)
      (Num.num_of_int 1) in
  Num.string_of_num (Num.div_num numerator denominator);;

let candle_case16594_native_input_interval term =
  let lower,upper = dest_pair term in
  candle_case16594_native_input_q_data lower ^ ":" ^
  candle_case16594_native_input_q_data upper;;

let candle_case16594_native_input_intervals terms =
  String.concat "," (map candle_case16594_native_input_interval terms);;

let rec candle_case16594_native_input_cval term =
  let constructor,arguments = strip_comb term in
  if aconv constructor `Cexp_num` then
    match arguments with
    | [value] -> "n" ^ Num.string_of_num (dest_numeral value)
    | _ -> failwith "case16594 native input: malformed cval numeral"
  else if aconv constructor `Cexp_pair` then
    match arguments with
    | [left;right] ->
        "p(" ^ candle_case16594_native_input_cval left ^ "," ^
        candle_case16594_native_input_cval right ^ ")"
    | _ -> failwith "case16594 native input: malformed cval pair"
  else failwith "case16594 native input: non-cval source program";;

let rec candle_case16594_native_input_program_length term =
  let constructor,arguments = strip_comb term in
  if aconv constructor `Cexp_num` then 0
  else if aconv constructor `Cexp_pair` then
    match arguments with
    | [_;tail] -> 1 + candle_case16594_native_input_program_length tail
    | _ -> failwith "case16594 native input: malformed program pair"
  else failwith "case16594 native input: malformed program spine";;

let rec candle_case16594_native_input_emit index = function
  | [] -> index
  | cell :: cells ->
      let stable = cell.variable_batch_stable_cell in
      if length cell.variable_batch_box_intervals <> 10 ||
         length stable.stable_batch_center_intervals <> 10 ||
         length stable.stable_batch_lower <> 6 ||
         length stable.stable_batch_upper <> 6 then
        failwith "case16594 native input: cell shape drift";
      print_endline
        ("CANDLE_CV_NL_NATIVE_JOB\t16594\t" ^ string_of_int index ^ "\t" ^
         candle_case16594_native_input_intervals
           cell.variable_batch_box_intervals ^ "\t" ^
         candle_case16594_native_input_intervals
           stable.stable_batch_center_intervals ^ "\t" ^
         candle_case16594_native_input_vector stable.stable_batch_lower ^
         "\t" ^
         candle_case16594_native_input_vector stable.stable_batch_upper);
      candle_case16594_native_input_emit (index + 1) cells;;

let _ =
  let axioms_before = axioms () in
  let captured = candle_disjunctive_case16594_complete_full_precomputed () in
  let source_program =
    captured.complete_full_prepared.program_representation_term in
  let program_length =
    candle_case16594_native_input_program_length source_program in
  if program_length <> 167 then
    failwith "case16594 native input: source program length drift";
  print_endline
    ("CANDLE_CV_NL_NATIVE_PROGRAM\t16594\t" ^
     candle_case16594_native_input_cval source_program);
  let emitted = candle_case16594_native_input_emit 0
    candle_disjunctive_case16594_variable_raw_plan_cells in
  let axioms_after = axioms () in
  if emitted <> 875 ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case16594 native input: validation failed";
  print_endline
    "CANDLE_CV_CASE16594_NATIVE_INPUTS_FULL_OK DEVELOPMENT_NON_RELEASE instructions=167 sqrt_slots=10 cells=875 assumptions=0 axiom_growth=0";;

end;;
