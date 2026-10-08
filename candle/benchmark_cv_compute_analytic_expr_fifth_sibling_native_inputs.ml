(* ========================================================================== *)
(* Export the fifth sibling batch's genuine 167-step numerical cells.        *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.  The program, square-root *)
(* certificates, centers, and boxes are ordinary diagnostic data.  This     *)
(* fragment creates no numerical verdict and introduces no theorem.          *)
(* ========================================================================== *)

module Benchmark_cv_compute_analytic_expr_fifth_sibling_native_inputs = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Candle_cv_analytic_expr_disjunctive_case16594_plan;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;
open Candle_cv_analytic_expr_disjunctive_fifth_sibling_batch_forest_plan;;

let candle_fifth_native_input_rational term =
  Num.string_of_num (rat_of_term term);;

let candle_fifth_native_input_vector terms =
  String.concat "," (map candle_fifth_native_input_rational terms);;

let candle_fifth_native_input_q_data term =
  let signed,denominator_predecessor = dest_pair term in
  let positive,negative = dest_pair signed in
  let numerator =
    Num.sub_num (dest_numeral positive) (dest_numeral negative) in
  let denominator =
    Num.add_num (dest_numeral denominator_predecessor)
      (Num.num_of_int 1) in
  Num.string_of_num (Num.div_num numerator denominator);;

let candle_fifth_native_input_interval term =
  let lower,upper = dest_pair term in
  candle_fifth_native_input_q_data lower ^ ":" ^
  candle_fifth_native_input_q_data upper;;

let candle_fifth_native_input_intervals terms =
  String.concat "," (map candle_fifth_native_input_interval terms);;

let rec candle_fifth_native_input_cval term =
  let constructor,arguments = strip_comb term in
  if aconv constructor `Cexp_num` then
    match arguments with
    | [value] -> "n" ^ Num.string_of_num (dest_numeral value)
    | _ -> failwith "fifth sibling native input: malformed cval numeral"
  else if aconv constructor `Cexp_pair` then
    match arguments with
    | [left;right] ->
        "p(" ^ candle_fifth_native_input_cval left ^ "," ^
        candle_fifth_native_input_cval right ^ ")"
    | _ -> failwith "fifth sibling native input: malformed cval pair"
  else failwith "fifth sibling native input: non-cval source program";;

let rec candle_fifth_native_input_program_length term =
  let constructor,arguments = strip_comb term in
  if aconv constructor `Cexp_num` then 0
  else if aconv constructor `Cexp_pair` then
    match arguments with
    | [_;tail] -> 1 + candle_fifth_native_input_program_length tail
    | _ -> failwith "fifth sibling native input: malformed program pair"
  else failwith "fifth sibling native input: malformed program spine";;

let rec candle_fifth_native_input_emit index = function
  | [] -> index
  | cell::cells ->
      let stable = cell.variable_batch_stable_cell in
      if length cell.variable_batch_box_intervals <> 10 ||
         length stable.stable_batch_center_intervals <> 10 ||
         length stable.stable_batch_lower <> 6 ||
         length stable.stable_batch_upper <> 6 then
        failwith "fifth sibling native input: cell shape drift";
      print_endline
        ("CANDLE_CV_NL_NATIVE_JOB\t16594\t" ^ string_of_int index ^ "\t" ^
         candle_fifth_native_input_intervals
           cell.variable_batch_box_intervals ^ "\t" ^
         candle_fifth_native_input_intervals
           stable.stable_batch_center_intervals ^ "\t" ^
         candle_fifth_native_input_vector stable.stable_batch_lower ^ "\t" ^
         candle_fifth_native_input_vector stable.stable_batch_upper);
      candle_fifth_native_input_emit (index + 1) cells;;

let _ =
  let axioms_before = axioms () in
  let source_program =
    candle_disjunctive_next_batch_prepared1.program_representation_term in
  if candle_fifth_native_input_program_length source_program <> 167 then
    failwith "fifth sibling native input: source program length drift";
  print_endline
    ("CANDLE_CV_NL_NATIVE_PROGRAM\t16594\t" ^
     candle_fifth_native_input_cval source_program);
  let emitted = candle_fifth_native_input_emit 0
    candle_disjunctive_fifth_batch_cells1 in
  let axioms_after = axioms () in
  if emitted <> 5869 ||
     length candle_disjunctive_fifth_batch_cells0 <> 1 ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "fifth sibling native input: validation failed";
  print_endline
    "CANDLE_CV_FIFTH_SIBLING_NATIVE_INPUTS_OK DEVELOPMENT_NON_RELEASE instructions=167 sqrt_slots=10 cells=5869 omitted_trivial_function0_cells=1 assumptions=0 axiom_growth=0";;

end;;
