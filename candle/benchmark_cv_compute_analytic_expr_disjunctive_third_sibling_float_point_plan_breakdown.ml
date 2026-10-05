(* Split shared point-certificate cost from exact versus float evaluation. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_third_sibling_float_point_plan.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_third_sibling_float_point_plan_breakdown = struct

open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;
open Benchmark_cv_compute_analytic_expr_disjunctive_third_sibling_float_point_plan;;

let candle_disjunctive_float_breakdown_axioms_before = axioms ();;

let candle_disjunctive_float_breakdown_bounds jobs =
  map
    (fun (_,_,_,domain) ->
      candle_disjunctive_fixed_outer_domain_bounds domain)
    jobs;;

print_endline
  "CANDLE_CV_FLOAT_POINT_BREAKDOWN_BOUNDS_BEGIN DEVELOPMENT_NON_RELEASE";;
let candle_disjunctive_float_breakdown_bounds0 =
  candle_disjunctive_float_breakdown_bounds
    candle_disjunctive_float_point_sample0;;
let candle_disjunctive_float_breakdown_bounds1 =
  candle_disjunctive_float_breakdown_bounds
    candle_disjunctive_float_point_sample1;;
print_endline
  "CANDLE_CV_FLOAT_POINT_BREAKDOWN_BOUNDS_END DEVELOPMENT_NON_RELEASE";;

let candle_disjunctive_float_breakdown_exact plan bounds =
  map
    (fun (lower,upper) ->
      candle_q_dim_taylor_model_point_plan_intervals_six plan lower upper)
    bounds;;

print_endline
  "CANDLE_CV_FLOAT_POINT_BREAKDOWN_EXACT_BEGIN DEVELOPMENT_NON_RELEASE";;
let candle_disjunctive_float_breakdown_exact0 =
  candle_disjunctive_float_breakdown_exact
    candle_disjunctive_next_batch_point_plan0
    candle_disjunctive_float_breakdown_bounds0;;
let candle_disjunctive_float_breakdown_exact1 =
  candle_disjunctive_float_breakdown_exact
    candle_disjunctive_next_batch_point_plan1
    candle_disjunctive_float_breakdown_bounds1;;
print_endline
  "CANDLE_CV_FLOAT_POINT_BREAKDOWN_EXACT_END DEVELOPMENT_NON_RELEASE";;

let candle_disjunctive_float_breakdown_float plan bounds =
  map
    (fun (lower,upper) ->
      candle_disjunctive_float_point_intervals plan lower upper)
    bounds;;

print_endline
  "CANDLE_CV_FLOAT_POINT_BREAKDOWN_FLOAT_BEGIN DEVELOPMENT_NON_RELEASE";;
let candle_disjunctive_float_breakdown_float0 =
  candle_disjunctive_float_breakdown_float
    candle_disjunctive_next_batch_point_plan0
    candle_disjunctive_float_breakdown_bounds0;;
let candle_disjunctive_float_breakdown_float1 =
  candle_disjunctive_float_breakdown_float
    candle_disjunctive_next_batch_point_plan1
    candle_disjunctive_float_breakdown_bounds1;;
print_endline
  "CANDLE_CV_FLOAT_POINT_BREAKDOWN_FLOAT_END DEVELOPMENT_NON_RELEASE";;

let candle_disjunctive_float_breakdown_axioms_after = axioms ();;
if length candle_disjunctive_float_breakdown_bounds0 <> 59 ||
   length candle_disjunctive_float_breakdown_bounds1 <> 1024 ||
   not
     (candle_disjunctive_float_point_equal_batches
       candle_disjunctive_float_breakdown_exact0
       candle_disjunctive_float_breakdown_float0) ||
   not
     (candle_disjunctive_float_point_equal_batches
       candle_disjunctive_float_breakdown_exact1
       candle_disjunctive_float_breakdown_float1) ||
   length candle_disjunctive_float_breakdown_axioms_after <>
     length candle_disjunctive_float_breakdown_axioms_before ||
   not
     (List.for_all
       (fun axiom ->
         List.mem axiom candle_disjunctive_float_breakdown_axioms_before)
       candle_disjunctive_float_breakdown_axioms_after) then
  failwith "float point plan breakdown: validation failed";;

print_endline
  "CANDLE_CV_FLOAT_POINT_PLAN_BREAKDOWN_OK DEVELOPMENT_NON_RELEASE jobs=1083 function0=59 function1=1024 exact_interval_terms_equal=true assumptions=0 axiom_growth=0";;

end;;
