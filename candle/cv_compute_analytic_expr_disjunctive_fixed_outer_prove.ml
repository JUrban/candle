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
open Candle_cv_analytic_expr_point_certificate_prepare;;
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

let candle_disjunctive_fixed_outer_widen_factors =
  [(5,4);(1001,1000);(101,100);(21,20);(11,10)];;

let candle_disjunctive_fixed_outer_factors_for_depth depth =
  if depth = 0 || depth >= 8 then
    candle_disjunctive_fixed_outer_widen_factors
  else [(5,4)];;

(* Keep restored-state clients away from ambiguous generative record labels. *)
let candle_disjunctive_fixed_outer_function_term prepared =
  prepared.function_term;;

let candle_disjunctive_fixed_outer_point_plan_program_count point_plan =
  length point_plan.point_plan_programs;;

let candle_disjunctive_fixed_outer_handoff
    prepared domain lower upper center_intervals box_intervals =
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

let candle_disjunctive_fixed_outer_attempt
    prepared point_plan numerator denominator domain =
  let lower,upper =
    candle_disjunctive_fixed_outer_domain_bounds domain in
  let center_intervals =
    candle_q_dim_taylor_model_point_plan_intervals_six
      point_plan lower upper in
  let box_intervals =
    map
      (candle_disjunctive_fixed_outer_widen numerator denominator)
      center_intervals in
  candle_disjunctive_fixed_outer_handoff
    prepared domain lower upper center_intervals box_intervals;;

(* Keep the generative point-plan record behind this module boundary.  A     *)
(* restored image may contain another record type with the same field labels. *)
let candle_disjunctive_fixed_outer_exact_intervals
    point_plan lower upper =
  let center_intervals =
    candle_q_dim_taylor_model_point_plan_intervals_six
      point_plan lower upper in
  let box_intervals =
    candle_q_box_rational_program_intervals_six
      point_plan.point_plan_programs lower upper in
  center_intervals,box_intervals;;

let candle_disjunctive_fixed_outer_exact_box_attempt
    prepared point_plan domain =
  let lower,upper =
    candle_disjunctive_fixed_outer_domain_bounds domain in
  let center_intervals,box_intervals =
    candle_disjunctive_fixed_outer_exact_intervals
      point_plan lower upper in
  candle_disjunctive_fixed_outer_handoff
    prepared domain lower upper center_intervals box_intervals;;

(* Tighten untrusted polynomial range hints without splitting the theorem   *)
(* domain: evaluate exact natural intervals on each of the 2^6 half-boxes,  *)
(* then take their hull.  The reflected checker still authenticates every   *)
(* resulting square-root enclosure before any theorem can be returned.      *)
let rec candle_disjunctive_fixed_outer_half_boxes = function
  | [] -> [[]]
  | (lower,upper) :: remaining ->
      let midpoint =
        Num.div_num (Num.add_num lower upper) (Num.num_of_int 2) in
      let tails =
        candle_disjunctive_fixed_outer_half_boxes remaining in
      map (fun tail -> (lower,midpoint) :: tail) tails @
      map (fun tail -> (midpoint,upper) :: tail) tails;;

let rec candle_disjunctive_fixed_outer_partition_boxes levels boxes =
  if levels = 0 then boxes
  else if levels < 0 then
    failwith "disjunctive fixed outer: negative partition level"
  else
    candle_disjunctive_fixed_outer_partition_boxes (levels - 1)
      (List.flatten
        (map candle_disjunctive_fixed_outer_half_boxes boxes));;

let candle_disjunctive_fixed_outer_interval_hull = function
  | [] -> failwith "disjunctive fixed outer: empty interval hull"
  | (first_lower,first_upper) :: remaining ->
      itlist
        (fun (lower,upper) (hull_lower,hull_upper) ->
          Num.min_num lower hull_lower,Num.max_num upper hull_upper)
        remaining (first_lower,first_upper);;

let candle_disjunctive_fixed_outer_partitioned_interval boxes program =
  candle_q_box_sqrt_interval
    (candle_disjunctive_fixed_outer_interval_hull
      (map
        (fun bounds ->
          candle_q_box_rational_program_interval bounds program)
        boxes));;

let candle_disjunctive_fixed_outer_partitioned_box_attempt_levels
    prepared point_plan levels domain =
  let lower,upper =
    candle_disjunctive_fixed_outer_domain_bounds domain in
  let center_intervals =
    candle_q_dim_taylor_model_point_plan_intervals_six
      point_plan lower upper in
  let bounds =
    map2
      (fun lower_term upper_term ->
        rat_of_term lower_term,rat_of_term upper_term)
      lower upper in
  let boxes =
    candle_disjunctive_fixed_outer_partition_boxes levels [bounds] in
  let box_intervals =
    map
      (candle_disjunctive_fixed_outer_partitioned_interval boxes)
      point_plan.point_plan_programs in
  candle_disjunctive_fixed_outer_handoff
    prepared domain lower upper center_intervals box_intervals;;

let candle_disjunctive_fixed_outer_partitioned_box_attempt
    prepared point_plan domain =
  candle_disjunctive_fixed_outer_partitioned_box_attempt_levels
    prepared point_plan 1 domain;;

(* Sample every corner of a six-dimensional box.  This is untrusted hint    *)
(* generation: the reflected checker rejects an enclosure that misses an    *)
(* interior extremum.  Compared with center-only relative widening, corner   *)
(* envelopes shrink with the source box and preserve much tighter jets.      *)
let rec candle_disjunctive_fixed_outer_corners lower upper =
  match lower,upper with
  | [],[] -> [[]]
  | lower_head::lower_tail,upper_head::upper_tail ->
      let remaining =
        candle_disjunctive_fixed_outer_corners lower_tail upper_tail in
      map (fun values -> lower_head :: values) remaining @
      map (fun values -> upper_head :: values) remaining
  | _ -> failwith "disjunctive fixed outer: corner shape";;

let candle_disjunctive_fixed_outer_corner_interval corners program =
  let values =
    map
      (fun point -> candle_q_point_rational_program_value point program)
      corners in
  match values with
  | [] -> failwith "disjunctive fixed outer: empty corner set"
  | first :: remaining ->
      let lower = itlist Num.min_num remaining first and
          upper = itlist Num.max_num remaining first in
      candle_q_box_sqrt_interval (lower,upper);;

let candle_disjunctive_fixed_outer_corner_attempt
    prepared point_plan numerator denominator domain =
  let lower,upper =
    candle_disjunctive_fixed_outer_domain_bounds domain in
  let center_intervals =
    candle_q_dim_taylor_model_point_plan_intervals_six
      point_plan lower upper in
  let corners =
    candle_disjunctive_fixed_outer_corners
      (map rat_of_term lower) (map rat_of_term upper) in
  let sampled =
    map
      (candle_disjunctive_fixed_outer_corner_interval corners)
      point_plan.point_plan_programs in
  let box_intervals =
    map
      (candle_disjunctive_fixed_outer_widen numerator denominator)
      sampled in
  candle_disjunctive_fixed_outer_handoff
    prepared domain lower upper center_intervals box_intervals;;

let candle_disjunctive_fixed_outer_prove
    prepared point_plan label attempts maximum_depth domain =
  let rec prove depth domain =
    let rec attempt_factors = function
      | [] -> None
      | (numerator,denominator) :: remaining ->
          attempts := !attempts + 1;
          let factor =
            string_of_int numerator ^ "/" ^ string_of_int denominator in
          print_endline
            ("CANDLE_CV_DISJUNCTIVE_FIXED_OUTER_ATTEMPT" ^
             " label=" ^ label ^
             " attempt=" ^ string_of_int !attempts ^
             " depth=" ^ string_of_int depth ^
             " factor=" ^ factor ^ " event=begin");
          try
            let theorem =
              candle_disjunctive_fixed_outer_attempt
                prepared point_plan numerator denominator domain in
            print_endline
              ("CANDLE_CV_DISJUNCTIVE_FIXED_OUTER_ATTEMPT" ^
               " label=" ^ label ^
               " attempt=" ^ string_of_int !attempts ^
               " depth=" ^ string_of_int depth ^
               " factor=" ^ factor ^ " event=accepted");
            Some theorem
          with Failure message ->
            if not (candle_disjunctive_fixed_outer_retryable message) then
              failwith
                ("disjunctive fixed outer: terminal attempt failure: " ^
                 message);
            print_endline
              ("CANDLE_CV_DISJUNCTIVE_FIXED_OUTER_ATTEMPT" ^
               " label=" ^ label ^
               " attempt=" ^ string_of_int !attempts ^
               " depth=" ^ string_of_int depth ^
               " factor=" ^ factor ^ " event=rejected");
            attempt_factors remaining in
    match attempt_factors
            (candle_disjunctive_fixed_outer_factors_for_depth depth) with
    | Some theorem ->
      {disjunctive_fixed_outer_theorem = theorem;
       disjunctive_fixed_outer_cells = 1;
       disjunctive_fixed_outer_max_depth = depth}
    | None ->
      if depth >= maximum_depth then
        failwith "disjunctive fixed outer: proposal depth limit";
      let axis = (depth mod 6) + 1 in
      print_endline
        ("CANDLE_CV_DISJUNCTIVE_FIXED_OUTER_SPLIT" ^
         " label=" ^ label ^
         " attempt=" ^ string_of_int !attempts ^
         " depth=" ^ string_of_int depth ^
         " axis=" ^ string_of_int axis ^
         " reason=all-bounded-proposals-rejected");
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
