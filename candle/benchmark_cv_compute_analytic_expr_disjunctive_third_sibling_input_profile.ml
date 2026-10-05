(* Print-suppressed profile of authentic reflected job-input construction. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_third_sibling_float_point_plan.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_third_sibling_input_profile = struct

open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;
open Benchmark_cv_compute_analytic_expr_disjunctive_third_sibling_float_point_plan;;

let _ =
  let axioms_before = axioms () in
  print_endline
    "CANDLE_CV_SIBLING_INPUT_PROFILE_BOUNDS_BEGIN DEVELOPMENT_NON_RELEASE";
  let bounds0 =
    map
      (fun (_,_,_,domain) ->
        candle_disjunctive_fixed_outer_domain_bounds domain)
      candle_disjunctive_float_point_sample0
  and bounds1 =
    map
      (fun (_,_,_,domain) ->
        candle_disjunctive_fixed_outer_domain_bounds domain)
      candle_disjunctive_float_point_sample1 in
  print_endline
    "CANDLE_CV_SIBLING_INPUT_PROFILE_BOUNDS_END DEVELOPMENT_NON_RELEASE";
  print_endline
    "CANDLE_CV_SIBLING_INPUT_PROFILE_EXACT_BEGIN DEVELOPMENT_NON_RELEASE";
  let exact0 =
    map
      (fun (lower,upper) ->
        candle_q_dim_taylor_model_point_plan_intervals_six
          candle_disjunctive_next_batch_point_plan0 lower upper)
      bounds0
  and exact1 =
    map
      (fun (lower,upper) ->
        candle_q_dim_taylor_model_point_plan_intervals_six
          candle_disjunctive_next_batch_point_plan1 lower upper)
      bounds1 in
  print_endline
    "CANDLE_CV_SIBLING_INPUT_PROFILE_EXACT_END DEVELOPMENT_NON_RELEASE";
  print_endline
    "CANDLE_CV_SIBLING_INPUT_PROFILE_FLOAT_BEGIN DEVELOPMENT_NON_RELEASE";
  let floated0 =
    map
      (fun (lower,upper) ->
        candle_disjunctive_float_point_intervals
          candle_disjunctive_next_batch_point_plan0 lower upper)
      bounds0
  and floated1 =
    map
      (fun (lower,upper) ->
        candle_disjunctive_float_point_intervals
          candle_disjunctive_next_batch_point_plan1 lower upper)
      bounds1 in
  print_endline
    "CANDLE_CV_SIBLING_INPUT_PROFILE_FLOAT_END DEVELOPMENT_NON_RELEASE";
  print_endline
    "CANDLE_CV_SIBLING_INPUT_PROFILE_CELLS_BEGIN DEVELOPMENT_NON_RELEASE";
  let make_cells bounds centers =
    map2
      (fun (lower,upper) center ->
        {variable_batch_box_intervals =
           map (candle_disjunctive_fixed_outer_widen 5 4) center;
         variable_batch_stable_cell =
           {stable_batch_center_intervals = center;
            stable_batch_lower = lower;
            stable_batch_upper = upper}})
      bounds centers in
  let cells0 = make_cells bounds0 exact0
  and cells1 = make_cells bounds1 exact1 in
  print_endline
    "CANDLE_CV_SIBLING_INPUT_PROFILE_CELLS_END DEVELOPMENT_NON_RELEASE";
  print_endline
    "CANDLE_CV_SIBLING_INPUT_PROFILE_ENCODE0_BEGIN DEVELOPMENT_NON_RELEASE";
  let _encoded0 =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
      cells0 in
  print_endline
    "CANDLE_CV_SIBLING_INPUT_PROFILE_ENCODE0_END DEVELOPMENT_NON_RELEASE";
  print_endline
    "CANDLE_CV_SIBLING_INPUT_PROFILE_ENCODE1_BEGIN DEVELOPMENT_NON_RELEASE";
  let _encoded1 =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
      cells1 in
  print_endline
    "CANDLE_CV_SIBLING_INPUT_PROFILE_ENCODE1_END DEVELOPMENT_NON_RELEASE";
  let axioms_after = axioms () in
  if length bounds0 <> 59 || length bounds1 <> 1024 ||
     length cells0 <> 59 || length cells1 <> 1024 ||
     not
       (candle_disjunctive_float_point_equal_batches exact0 floated0) ||
     not
       (candle_disjunctive_float_point_equal_batches exact1 floated1) ||
     length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun axiom -> List.mem axiom axioms_before)
         axioms_after) then
    failwith "sibling input profile: validation failed";
  print_endline
    "CANDLE_CV_SIBLING_INPUT_PROFILE_OK DEVELOPMENT_NON_RELEASE jobs=1083 function0=59 function1=1024 exact_interval_terms_equal=true assumptions=0 axiom_growth=0";;

end;;
