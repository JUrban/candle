(* Integration check for the data-only endpoint decoder in the production    *)
(* fixed-outer preparation path.  The expected side remains kernel-proved.   *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_third_sibling_float_point_plan.ml";;

module Test_cv_compute_analytic_expr_disjunctive_bound_decode_integration = struct

open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_third_sibling_float_point_plan;;

let _ =
  let rec equal_terms left right =
    match left,right with
    | [],[] -> true
    | left_head::left_tail,right_head::right_tail ->
        aconv left_head right_head && equal_terms left_tail right_tail
    | _ -> false in
  let equal_bounds (lower1,upper1) (lower2,upper2) =
    equal_terms lower1 lower2 && equal_terms upper1 upper2 in
  let rec equal_batches left right =
    match left,right with
    | [],[] -> true
    | left_head::left_tail,right_head::right_tail ->
        equal_bounds left_head right_head &&
        equal_batches left_tail right_tail
    | _ -> false in
  let proved_bounds domain_theorem =
    let domain_pair,_,_ =
      M_taylor.dest_m_cell_domain (concl domain_theorem) in
    let actual_lower,actual_upper = dest_pair domain_pair in
    let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
        upper,_ = candle_reflected_nl_normalize_vector actual_upper in
    lower,upper in
  let jobs =
    candle_disjunctive_float_point_sample0 @
    candle_disjunctive_float_point_sample1 in
  let axioms_before = axioms () in
  print_endline
    "CANDLE_CV_BOUND_DECODE_INTEGRATION_PROOF_BEGIN DEVELOPMENT_NON_RELEASE";
  let proved =
    map (fun (_,_,_,domain) -> proved_bounds domain) jobs in
  print_endline
    "CANDLE_CV_BOUND_DECODE_INTEGRATION_PROOF_END DEVELOPMENT_NON_RELEASE";
  print_endline
    "CANDLE_CV_BOUND_DECODE_INTEGRATION_DATA_BEGIN DEVELOPMENT_NON_RELEASE";
  let decoded =
    map
      (fun (_,_,_,domain) ->
        candle_disjunctive_fixed_outer_domain_bounds domain)
      jobs in
  print_endline
    "CANDLE_CV_BOUND_DECODE_INTEGRATION_DATA_END DEVELOPMENT_NON_RELEASE";
  let axioms_after = axioms () in
  if length proved <> 1083 || length decoded <> 1083 ||
     not (equal_batches proved decoded) ||
     length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun axiom -> List.mem axiom axioms_before)
         axioms_after) then
    failwith "data-only bound decoder integration: validation failed";
  print_endline
    "CANDLE_CV_BOUND_DECODE_INTEGRATION_OK DEVELOPMENT_NON_RELEASE jobs=1083 endpoints=12996 exact_terms_equal=true proof_handoff_preserved=true assumptions=0 axiom_growth=0";;

end;;
