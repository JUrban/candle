(* Matched real-leaf discriminator for per-job reflected certificates. *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_batch = struct

open Certificate;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;
open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;

let candle_disjunctive_case16594_variable_axioms_before = axioms ();;

Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
  (fun event ->
    print_endline
      ("CANDLE_CERT_PROFILE lane=disjunctive-case16594-variable-batch" ^
       " phase=" ^ event));;

let rec candle_disjunctive_case16594_variable_take count items =
  if count = 0 then []
  else
    match items with
    | [] -> failwith "case16594 variable batch: short leaf list"
    | head :: tail ->
        head ::
        candle_disjunctive_case16594_variable_take (count - 1) tail;;

let candle_disjunctive_case16594_variable_make_cell (_,domain) =
  let lower,upper =
    candle_disjunctive_fixed_outer_domain_bounds domain in
  let center_intervals =
    candle_q_dim_taylor_model_point_plan_intervals_six
      candle_disjunctive_case16594_engine_state.family_engine_point_plan
      lower upper in
  let box_intervals =
    map (candle_disjunctive_fixed_outer_widen 5 4) center_intervals in
  {variable_batch_box_intervals = box_intervals;
   variable_batch_stable_cell =
     {stable_batch_center_intervals = center_intervals;
      stable_batch_lower = lower;
      stable_batch_upper = upper}};;

let candle_disjunctive_case16594_variable_leaves_32 =
  candle_disjunctive_case16594_variable_take 32
    candle_disjunctive_case16594_engine_state.family_engine_leaves;;
let candle_disjunctive_case16594_variable_cells_32 =
  map candle_disjunctive_case16594_variable_make_cell
    candle_disjunctive_case16594_variable_leaves_32;;

let candle_disjunctive_case16594_variable_validate_pass
    domain theorem =
  let functions,proved_domain =
    M_verifier.dest_m_cell_list_pass (concl theorem) in
  let expected_domain,_,_ = M_taylor.dest_m_cell_domain (concl domain) in
  if functions <>
       [candle_disjunctive_case16594_engine_state.
          family_engine_function_term] ||
     not (aconv proved_domain expected_domain) ||
     hyp theorem <> [] then
    failwith "case16594 variable batch: pass theorem mismatch";;

let candle_disjunctive_case16594_variable_handoff
    leaves cells sources =
  let rec build leaves cells sources =
    match leaves,cells,sources with
    | [],[],[] -> []
    | (_,domain) :: leaf_tail,cell :: cell_tail,source :: source_tail ->
        let stable = cell.variable_batch_stable_cell in
        let theorem =
          candle_reflected_nl_source_pass_with
            candle_disjunctive_case16594_engine_state.
              family_engine_function_term
            (fun actual_lower actual_upper ->
              if not
                  (candle_disjunctive_fixed_outer_aconv_lists
                     actual_lower stable.stable_batch_lower &&
                   candle_disjunctive_fixed_outer_aconv_lists
                     actual_upper stable.stable_batch_upper) then
                failwith "case16594 variable batch: handoff box drift";
              source)
            domain in
        candle_disjunctive_case16594_variable_validate_pass domain theorem;
        theorem :: build leaf_tail cell_tail source_tail
    | _ -> failwith "case16594 variable batch: handoff length mismatch" in
  build leaves cells sources;;

type candle_disjunctive_case16594_variable_result = {
  variable_count : int;
  variable_theorems : thm list;
};;

let candle_disjunctive_case16594_variable_run count =
  let leaves =
    candle_disjunctive_case16594_variable_take count
      candle_disjunctive_case16594_variable_leaves_32 and
      cells =
        candle_disjunctive_case16594_variable_take count
          candle_disjunctive_case16594_variable_cells_32 in
  let result =
    candle_q_dim_taylor_model_fixed_outer_variable_batch_prove_six
      candle_disjunctive_case16594_engine_state.family_engine_prepared
      cells in
  let sources =
    candle_q_dim_taylor_model_fixed_outer_variable_batch_sources_six
      result in
  let theorems =
    candle_disjunctive_case16594_variable_handoff
      leaves cells sources in
  {variable_count = count;
   variable_theorems = theorems};;

let candle_disjunctive_case16594_variable_result_1 =
  candle_disjunctive_case16594_variable_run 1;;
let candle_disjunctive_case16594_variable_result_8 =
  candle_disjunctive_case16594_variable_run 8;;
let candle_disjunctive_case16594_variable_result_32 =
  candle_disjunctive_case16594_variable_run 32;;

let candle_disjunctive_case16594_variable_expect_rejection label cell =
  try
    let _ =
      candle_q_dim_taylor_model_fixed_outer_variable_batch_prove_six
        candle_disjunctive_case16594_engine_state.family_engine_prepared
        [cell] in
    failwith
      ("case16594 variable batch: accepted malformed " ^ label)
  with Failure message ->
    if message <>
         "fixed outer variable batch prover: numerical batch rejected" then
      failwith
        ("case16594 variable batch: unexpected " ^ label ^
         " rejection: " ^ message);;

let candle_disjunctive_case16594_variable_first_cell =
  hd candle_disjunctive_case16594_variable_cells_32;;
let candle_disjunctive_case16594_variable_bad_box_hints =
  {candle_disjunctive_case16594_variable_first_cell with
   variable_batch_box_intervals =
     tl
       candle_disjunctive_case16594_variable_first_cell.
         variable_batch_box_intervals};;
let candle_disjunctive_case16594_variable_bad_center_hints =
  let cell = candle_disjunctive_case16594_variable_first_cell in
  {cell with
   variable_batch_stable_cell =
     {cell.variable_batch_stable_cell with
      stable_batch_center_intervals =
        tl cell.variable_batch_stable_cell.stable_batch_center_intervals}};;
let _ =
  candle_disjunctive_case16594_variable_expect_rejection
    "whole-box-hint-count"
    candle_disjunctive_case16594_variable_bad_box_hints;;
let _ =
  candle_disjunctive_case16594_variable_expect_rejection
    "center-hint-count"
    candle_disjunctive_case16594_variable_bad_center_hints;;
print_endline
  "CANDLE_CV_DISJUNCTIVE_CASE16594_VARIABLE_BATCH_REJECTION_OK cases=2";;

let candle_disjunctive_case16594_variable_digest result =
  Digest.to_hex
    (Digest.string
      (String.concat "\n" (map string_of_thm result.variable_theorems)));;

let rec candle_disjunctive_case16594_variable_prefix_equal left right =
  match left,right with
  | [],_ -> true
  | _,[] -> false
  | left_head :: left_tail,right_head :: right_tail ->
      hyp left_head = hyp right_head &&
      aconv (concl left_head) (concl right_head) &&
      candle_disjunctive_case16594_variable_prefix_equal
        left_tail right_tail;;

let candle_disjunctive_case16594_variable_axioms_after = axioms ();;
if length
     candle_disjunctive_case16594_variable_result_1.variable_theorems <> 1 ||
   length
     candle_disjunctive_case16594_variable_result_8.variable_theorems <> 8 ||
   length
     candle_disjunctive_case16594_variable_result_32.variable_theorems <> 32 ||
   not
     (candle_disjunctive_case16594_variable_prefix_equal
       candle_disjunctive_case16594_variable_result_1.variable_theorems
       candle_disjunctive_case16594_variable_result_8.variable_theorems) ||
   not
     (candle_disjunctive_case16594_variable_prefix_equal
       candle_disjunctive_case16594_variable_result_8.variable_theorems
       candle_disjunctive_case16594_variable_result_32.variable_theorems) ||
   length candle_disjunctive_case16594_variable_axioms_after <>
     length candle_disjunctive_case16594_variable_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_disjunctive_case16594_variable_axioms_before)
       candle_disjunctive_case16594_variable_axioms_after) then
  failwith "case16594 variable batch: final validation failed";;

let candle_disjunctive_case16594_variable_print result =
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_CASE16594_VARIABLE_BATCH_RESULT" ^
     " boxes=" ^ string_of_int result.variable_count ^
     " theorem_digest=" ^
     candle_disjunctive_case16594_variable_digest result);;

let _ =
  candle_disjunctive_case16594_variable_print
    candle_disjunctive_case16594_variable_result_1;;
let _ =
  candle_disjunctive_case16594_variable_print
    candle_disjunctive_case16594_variable_result_8;;
let _ =
  candle_disjunctive_case16594_variable_print
    candle_disjunctive_case16594_variable_result_32;;
print_endline
  "CANDLE_CV_DISJUNCTIVE_CASE16594_VARIABLE_BATCH_OK DEVELOPMENT_NON_RELEASE";;

end;;
