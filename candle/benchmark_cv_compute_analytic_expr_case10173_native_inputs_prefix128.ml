(* ========================================================================== *)
(* Export the exact current fixed-nonlinear inputs for a native discriminator. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.  The exported source       *)
(* program, square-root certificates, and boxes are ordinary diagnostic data. *)
(* This fragment creates no numerical verdict or theorem evidence.            *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_variable_raw_plan.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_native_inputs_prefix128 = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Benchmark_cv_compute_analytic_expr_case10173_variable_raw_plan;;

let candle_case10173_native_input_rational term =
  Num.string_of_num (rat_of_term term);;

let candle_case10173_native_input_vector terms =
  String.concat "," (map candle_case10173_native_input_rational terms);;

let candle_case10173_native_input_q_data term =
  let signed,denominator_predecessor = dest_pair term in
  let positive,negative = dest_pair signed in
  let numerator =
    Num.sub_num (dest_numeral positive) (dest_numeral negative) in
  let denominator =
    Num.add_num (dest_numeral denominator_predecessor)
      (Num.num_of_int 1) in
  Num.string_of_num (Num.div_num numerator denominator);;

let candle_case10173_native_input_interval term =
  let lower,upper = dest_pair term in
  candle_case10173_native_input_q_data lower ^ ":" ^
  candle_case10173_native_input_q_data upper;;

let candle_case10173_native_input_intervals terms =
  String.concat "," (map candle_case10173_native_input_interval terms);;

let rec candle_case10173_native_input_cval term =
  let constructor,arguments = strip_comb term in
  if aconv constructor `Cexp_num` then
    match arguments with
    | [value] -> "n" ^ Num.string_of_num (dest_numeral value)
    | _ -> failwith "case10173 native input: malformed cval numeral"
  else if aconv constructor `Cexp_pair` then
    match arguments with
    | [left;right] ->
        "p(" ^ candle_case10173_native_input_cval left ^ "," ^
        candle_case10173_native_input_cval right ^ ")"
    | _ -> failwith "case10173 native input: malformed cval pair"
  else failwith "case10173 native input: non-cval source program";;

let rec candle_case10173_native_input_program_length term =
  let constructor,arguments = strip_comb term in
  if aconv constructor `Cexp_num` then 0
  else if aconv constructor `Cexp_pair` then
    match arguments with
    | [_;tail] -> 1 + candle_case10173_native_input_program_length tail
    | _ -> failwith "case10173 native input: malformed program pair"
  else failwith "case10173 native input: malformed program spine";;

let rec candle_case10173_native_input_emit index remaining = function
  | _ when remaining = 0 -> ()
  | [] -> failwith "case10173 native input: short cell plan"
  | cell :: cells ->
      let stable = cell.variable_batch_stable_cell in
      if length cell.variable_batch_box_intervals <> 7 ||
         length stable.stable_batch_center_intervals <> 7 ||
         length stable.stable_batch_lower <> 6 ||
         length stable.stable_batch_upper <> 6 then
        failwith "case10173 native input: cell shape drift";
      print_endline
        ("CANDLE_CV_NL_NATIVE_JOB\t10173\t" ^ string_of_int index ^ "\t" ^
         candle_case10173_native_input_intervals
           cell.variable_batch_box_intervals ^ "\t" ^
         candle_case10173_native_input_intervals
           stable.stable_batch_center_intervals ^ "\t" ^
         candle_case10173_native_input_vector stable.stable_batch_lower ^
         "\t" ^
         candle_case10173_native_input_vector stable.stable_batch_upper);
      candle_case10173_native_input_emit (index + 1) (remaining - 1) cells;;

let _ =
  let axioms_before = axioms () in
  let plan = candle_case10173_variable_raw_plan () in
  let prepared = plan.case10173_variable_raw_plan_prepared in
  let source_program =
    prepared.program_representation_term in
  let program_length =
    candle_case10173_native_input_program_length source_program in
  if program_length <> 54 then
    failwith "case10173 native input: source program length drift";
  print_endline
    ("CANDLE_CV_NL_NATIVE_PROGRAM\t10173\t" ^
     candle_case10173_native_input_cval source_program);
  candle_case10173_native_input_emit 0 128
    plan.case10173_variable_raw_plan_cells;
  let axioms_after = axioms () in
  if length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case10173 native input: axiom-set drift";
  print_endline
    "CANDLE_CV_CASE10173_NATIVE_INPUTS_PREFIX128_OK DEVELOPMENT_NON_RELEASE instructions=54 sqrt_slots=7 cells=128 assumptions=0 axiom_growth=0";;

end;;
