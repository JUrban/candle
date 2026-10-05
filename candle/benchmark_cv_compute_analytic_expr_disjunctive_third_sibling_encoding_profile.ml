(* Phase profile for raw reflected-job encoding after fast endpoint decoding. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_third_sibling_float_point_plan.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_third_sibling_encoding_profile = struct

open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;
open Benchmark_cv_compute_analytic_expr_disjunctive_third_sibling_float_point_plan;;

let _ =
  let rec map3 function_ left middle right =
    match left,middle,right with
    | [],[],[] -> []
    | left_head::left_tail,middle_head::middle_tail,right_head::right_tail ->
        function_ left_head middle_head right_head ::
        map3 function_ left_tail middle_tail right_tail
    | _ -> failwith "sibling encoding profile: map3 shape" in
  let axioms_before = axioms () in
  print_endline
    "CANDLE_CV_SIBLING_ENCODING_BOUNDS_BEGIN DEVELOPMENT_NON_RELEASE";
  let bounds =
    map
      (fun (_,_,_,domain) ->
        candle_disjunctive_fixed_outer_domain_bounds domain)
      candle_disjunctive_float_point_sample1 in
  print_endline
    "CANDLE_CV_SIBLING_ENCODING_BOUNDS_END DEVELOPMENT_NON_RELEASE";
  print_endline
    "CANDLE_CV_SIBLING_ENCODING_CENTERS_BEGIN DEVELOPMENT_NON_RELEASE";
  let centers =
    map
      (fun (lower,upper) ->
        candle_q_dim_taylor_model_point_plan_intervals_six
          candle_disjunctive_next_batch_point_plan1 lower upper)
      bounds in
  print_endline
    "CANDLE_CV_SIBLING_ENCODING_CENTERS_END DEVELOPMENT_NON_RELEASE";
  print_endline
    "CANDLE_CV_SIBLING_ENCODING_CELLS_BEGIN DEVELOPMENT_NON_RELEASE";
  let cells =
    map2
      (fun (lower,upper) center ->
        {variable_batch_box_intervals =
           map (candle_disjunctive_fixed_outer_widen 5 4) center;
         variable_batch_stable_cell =
           {stable_batch_center_intervals = center;
            stable_batch_lower = lower;
            stable_batch_upper = upper}})
      bounds centers in
  print_endline
    "CANDLE_CV_SIBLING_ENCODING_CELLS_END DEVELOPMENT_NON_RELEASE";
  print_endline
    "CANDLE_CV_SIBLING_ENCODING_SOURCE_BOXES_BEGIN DEVELOPMENT_NON_RELEASE";
  let source_boxes =
    map
      (fun cell ->
        let stable = cell.variable_batch_stable_cell in
        dest_list
          (candle_poly_fixture_q_boxes
            stable.stable_batch_lower stable.stable_batch_upper))
      cells in
  print_endline
    "CANDLE_CV_SIBLING_ENCODING_SOURCE_BOXES_END DEVELOPMENT_NON_RELEASE";
  print_endline
    "CANDLE_CV_SIBLING_ENCODING_OUTER_BEGIN DEVELOPMENT_NON_RELEASE";
  let encoded_outer =
    map
      (fun cell ->
        candle_q_dim_stable_program_encode_intervals
          cell.variable_batch_box_intervals)
      cells in
  print_endline
    "CANDLE_CV_SIBLING_ENCODING_OUTER_END DEVELOPMENT_NON_RELEASE";
  print_endline
    "CANDLE_CV_SIBLING_ENCODING_CENTER_BEGIN DEVELOPMENT_NON_RELEASE";
  let encoded_center =
    map
      (fun cell ->
        candle_q_dim_stable_program_encode_intervals
          cell.variable_batch_stable_cell.stable_batch_center_intervals)
      cells in
  print_endline
    "CANDLE_CV_SIBLING_ENCODING_CENTER_END DEVELOPMENT_NON_RELEASE";
  print_endline
    "CANDLE_CV_SIBLING_ENCODING_SOURCE_BEGIN DEVELOPMENT_NON_RELEASE";
  let encoded_source =
    map candle_q_dim_stable_program_encode_intervals source_boxes in
  print_endline
    "CANDLE_CV_SIBLING_ENCODING_SOURCE_END DEVELOPMENT_NON_RELEASE";
  print_endline
    "CANDLE_CV_SIBLING_ENCODING_CELL_ASSEMBLY_BEGIN DEVELOPMENT_NON_RELEASE";
  let encoded_cells =
    map3
      (fun outer center source ->
        candle_q_dim_stable_program_cval_pair outer
          (candle_q_dim_stable_program_cval_pair center source))
      encoded_outer encoded_center encoded_source in
  print_endline
    "CANDLE_CV_SIBLING_ENCODING_CELL_ASSEMBLY_END DEVELOPMENT_NON_RELEASE";
  print_endline
    "CANDLE_CV_SIBLING_ENCODING_LIST_SPINE_BEGIN DEVELOPMENT_NON_RELEASE";
  let staged = candle_q_dim_stable_program_cval_list encoded_cells in
  print_endline
    "CANDLE_CV_SIBLING_ENCODING_LIST_SPINE_END DEVELOPMENT_NON_RELEASE";
  print_endline
    "CANDLE_CV_SIBLING_ENCODING_BASELINE_BEGIN DEVELOPMENT_NON_RELEASE";
  let baseline =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
      cells in
  print_endline
    "CANDLE_CV_SIBLING_ENCODING_BASELINE_END DEVELOPMENT_NON_RELEASE";
  let axioms_after = axioms () in
  if length bounds <> 1024 || length centers <> 1024 ||
     length cells <> 1024 || length source_boxes <> 1024 ||
     length encoded_outer <> 1024 || length encoded_center <> 1024 ||
     length encoded_source <> 1024 || length encoded_cells <> 1024 ||
     not (aconv staged baseline) ||
     length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun axiom -> List.mem axiom axioms_before)
         axioms_after) then
    failwith "sibling encoding profile: validation failed";
  print_endline
    "CANDLE_CV_SIBLING_ENCODING_PROFILE_OK DEVELOPMENT_NON_RELEASE jobs=1024 staged_term_equal=true assumptions=0 axiom_growth=0";;

end;;
