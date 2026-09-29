(* ========================================================================== *)
(* Reflected fixed-outer prover for an ordinary disjunctive verifier leaf.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is deliberately independent of any one  *)
(* leaf index.  It retries only the two expected numerical-preparation       *)
(* failures, proves every accepted child through Kernel.compute, and glues   *)
(* the children back to the exact authenticated input domain theorem.  The   *)
(* whole-box square-root proposal is an untrusted widening of exact center   *)
(* values; rejection merely triggers authenticated subdivision.              *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_box_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_certificate_variant_prepare.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_stable_batch_prove.ml";;

module Candle_cv_analytic_expr_disjunctive_fixed_outer_prove = struct

open Certificate;;
open Candle_cv_exact_interval_reify;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_stable_batch_prove;;

type candle_disjunctive_fixed_outer_result = {
  disjunctive_fixed_outer_theorem : thm;
  disjunctive_fixed_outer_cells : int;
  disjunctive_fixed_outer_max_depth : int;
};;

let candle_disjunctive_fixed_outer_domain_bounds domain_theorem =
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_theorem) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
      upper,_ = candle_reflected_nl_normalize_vector actual_upper in
  lower,upper;;

let rec candle_disjunctive_fixed_outer_aconv_lists left right =
  match left,right with
  | [],[] -> true
  | left_head::left_tail,right_head::right_tail ->
      aconv left_head right_head &&
      candle_disjunctive_fixed_outer_aconv_lists left_tail right_tail
  | _ -> false;;

let candle_disjunctive_fixed_outer_retryable = function
  | "fixed outer stable Taylor batch prover: numerical batch rejected" -> true
  | _ -> false;;

let candle_disjunctive_fixed_outer_q_num value =
  let signed,denominator_predecessor = dest_pair value in
  let positive,negative = dest_pair signed in
  Num.div_num
    (Num.sub_num (dest_numeral positive) (dest_numeral negative))
    (Num.add_num
      (dest_numeral denominator_predecessor) (Num.num_of_int 1));;

let candle_disjunctive_fixed_outer_widen numerator denominator interval =
  let lower,upper = dest_pair interval in
  let factor =
    Num.div_num (Num.num_of_int numerator) (Num.num_of_int denominator) in
  mk_pair
    (candle_q_term
      (Num.div_num (candle_disjunctive_fixed_outer_q_num lower) factor),
     candle_q_term
      (Num.mul_num (candle_disjunctive_fixed_outer_q_num upper) factor));;

let candle_disjunctive_fixed_outer_widen_numerator = 5;;
let candle_disjunctive_fixed_outer_widen_denominator = 4;;

let candle_disjunctive_fixed_outer_attempt
    prepared point_plan domain =
  let lower,upper =
    candle_disjunctive_fixed_outer_domain_bounds domain in
  let center_intervals =
    candle_q_dim_taylor_model_point_plan_intervals_six
      point_plan lower upper in
  let box_intervals =
    map
      (candle_disjunctive_fixed_outer_widen
        candle_disjunctive_fixed_outer_widen_numerator
        candle_disjunctive_fixed_outer_widen_denominator)
      center_intervals in
  if length box_intervals <> 10 || length center_intervals <> 10 then
    failwith "disjunctive fixed outer: square-root slot drift";
  let cell =
    {stable_batch_center_intervals = center_intervals;
     stable_batch_lower = lower;
     stable_batch_upper = upper} in
  let aggregate =
    candle_q_dim_taylor_model_fixed_outer_stable_batch_prove_six
      prepared box_intervals [cell] in
  let source =
    candle_q_dim_taylor_model_fixed_outer_stable_batch_cell_source_six
      aggregate cell in
  candle_reflected_nl_source_pass_with prepared.function_term
    (fun actual_lower actual_upper ->
      if not
          (candle_disjunctive_fixed_outer_aconv_lists
             actual_lower lower &&
           candle_disjunctive_fixed_outer_aconv_lists
             actual_upper upper) then
        failwith "disjunctive fixed outer: unexpected handoff box";
      source)
    domain;;

let candle_disjunctive_fixed_outer_prove
    prepared point_plan label attempts maximum_depth domain =
  let rec prove depth domain =
    attempts := !attempts + 1;
    print_endline
      ("CANDLE_CV_DISJUNCTIVE_FIXED_OUTER_ATTEMPT" ^
       " label=" ^ label ^
       " attempt=" ^ string_of_int !attempts ^
       " depth=" ^ string_of_int depth ^ " event=begin");
    try
      let theorem =
        candle_disjunctive_fixed_outer_attempt prepared point_plan domain in
      print_endline
        ("CANDLE_CV_DISJUNCTIVE_FIXED_OUTER_ATTEMPT" ^
         " label=" ^ label ^
         " attempt=" ^ string_of_int !attempts ^
         " depth=" ^ string_of_int depth ^ " event=accepted");
      {disjunctive_fixed_outer_theorem = theorem;
       disjunctive_fixed_outer_cells = 1;
       disjunctive_fixed_outer_max_depth = depth}
    with Failure message ->
      if depth >= maximum_depth ||
         not (candle_disjunctive_fixed_outer_retryable message) then
        failwith
          ("disjunctive fixed outer: terminal attempt failure: " ^ message);
      let axis = (depth mod 6) + 1 in
      print_endline
        ("CANDLE_CV_DISJUNCTIVE_FIXED_OUTER_SPLIT" ^
         " label=" ^ label ^
         " attempt=" ^ string_of_int !attempts ^
         " depth=" ^ string_of_int depth ^
         " axis=" ^ string_of_int axis ^
         " reason=" ^ message);
      let left_domain,right_domain =
        M_verifier.split_domain 6 6 axis domain in
      let left = prove (depth + 1) left_domain in
      let right = prove (depth + 1) right_domain in
      let appended =
        M_verifier.m_glue_cells_list 6 axis
          left.disjunctive_fixed_outer_theorem
          right.disjunctive_fixed_outer_theorem in
      {disjunctive_fixed_outer_theorem =
         M_verifier.merge_m_cell_list_pass 6 appended;
       disjunctive_fixed_outer_cells =
         left.disjunctive_fixed_outer_cells +
         right.disjunctive_fixed_outer_cells;
       disjunctive_fixed_outer_max_depth =
         max left.disjunctive_fixed_outer_max_depth
           right.disjunctive_fixed_outer_max_depth} in
  prove 0 domain;;

end;;
