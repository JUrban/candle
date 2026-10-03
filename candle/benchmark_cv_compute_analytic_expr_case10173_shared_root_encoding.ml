(* ========================================================================== *)
(* Shared-root job encoding experiment for complete genuine case 10173.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Every final cell under one adaptive root has  *)
(* the same whole-box square-root intervals.  Encode that payload once per   *)
(* root, retain the existing center/domain payload per cell, and compare the  *)
(* resulting complete cval term with the preserved accepted input.           *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_complete_capture.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_shared_root_encoding = struct

open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Benchmark_cv_compute_analytic_expr_case10173_variable_raw_plan;;
open Benchmark_cv_compute_analytic_expr_case10173_complete_capture;;

type candle_case10173_shared_root_payload = {
  case10173_shared_root_box : term;
  case10173_shared_root_cells :
    candle_q_dim_taylor_model_fixed_outer_variable_batch_cell_six list;
};;

type candle_case10173_shared_root_cell = {
  case10173_shared_root_cell_box : term;
  case10173_shared_root_cell_source :
    candle_q_dim_taylor_model_fixed_outer_variable_batch_cell_six;
};;

let rec candle_case10173_shared_root_reverse_append items result =
  match items with
  | [] -> result
  | head :: tail ->
      candle_case10173_shared_root_reverse_append tail (head :: result);;

let rec candle_case10173_shared_root_flatten roots reversed =
  match roots with
  | [] -> rev reversed
  | root :: remaining ->
      let cells =
        map
          (fun cell -> {
            case10173_shared_root_cell_box = root.case10173_shared_root_box;
            case10173_shared_root_cell_source = cell;
          })
          root.case10173_shared_root_cells in
      candle_case10173_shared_root_flatten remaining
        (candle_case10173_shared_root_reverse_append cells reversed);;

let rec candle_case10173_shared_root_map3 action first second third =
  match first,second,third with
  | [],[],[] -> []
  | first_head :: first_tail,
    second_head :: second_tail,
    third_head :: third_tail ->
      action first_head second_head third_head ::
      candle_case10173_shared_root_map3
        action first_tail second_tail third_tail
  | _ -> failwith "case10173 shared-root encoding: map3 shape";;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE lane=case10173-shared-root-encoding" ^
         " phase=" ^ event));
  let axioms_before = axioms () in
  let plan = candle_case10173_variable_raw_plan () in
  let captured = candle_case10173_complete_capture () in
  candle_q_dim_analytic_jet_profile_event
    "shared-root-box-encoding-begin";
  let roots =
    map
      (fun (root : candle_case10173_variable_raw_root) -> {
        case10173_shared_root_box =
          candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_intervals
            root.case10173_variable_raw_root_box_intervals;
        case10173_shared_root_cells =
          root.case10173_variable_raw_root_cells;
      })
      plan.case10173_variable_raw_plan_roots in
  candle_q_dim_analytic_jet_profile_event
    "shared-root-box-encoding-end";
  candle_q_dim_analytic_jet_profile_event
    "shared-root-flatten-begin";
  let cells = candle_case10173_shared_root_flatten roots [] in
  candle_q_dim_analytic_jet_profile_event
    "shared-root-flatten-end";
  candle_q_dim_analytic_jet_profile_event
    "shared-root-center-encoding-begin";
  let encoded_centers =
    map
      (fun (cell : candle_case10173_shared_root_cell) ->
        candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_intervals
          cell.case10173_shared_root_cell_source.
            variable_batch_stable_cell.stable_batch_center_intervals)
      cells in
  candle_q_dim_analytic_jet_profile_event
    "shared-root-center-encoding-end";
  candle_q_dim_analytic_jet_profile_event
    "shared-root-domain-encoding-begin";
  let encoded_domains =
    map
      (fun (cell : candle_case10173_shared_root_cell) ->
        let stable =
          cell.case10173_shared_root_cell_source.variable_batch_stable_cell in
        if length stable.stable_batch_lower <> 6 ||
           length stable.stable_batch_upper <> 6 then
          failwith "case10173 shared-root encoding: expected six coordinates";
        candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_intervals
          (dest_list
            (candle_poly_fixture_q_boxes
              stable.stable_batch_lower stable.stable_batch_upper)))
      cells in
  candle_q_dim_analytic_jet_profile_event
    "shared-root-domain-encoding-end";
  candle_q_dim_analytic_jet_profile_event
    "shared-root-list-assembly-begin";
  let encoded_cells =
    candle_case10173_shared_root_map3
      (fun (cell : candle_case10173_shared_root_cell) center domain ->
        candle_q_dim_stable_program_cval_pair
          cell.case10173_shared_root_cell_box
          (candle_q_dim_stable_program_cval_pair center domain))
      cells encoded_centers encoded_domains in
  let encoded_jobs =
    candle_q_dim_stable_program_cval_list encoded_cells in
  candle_q_dim_analytic_jet_profile_event
    "shared-root-list-assembly-end";
  candle_q_dim_analytic_jet_profile_event
    "shared-root-identity-check-begin";
  let identical =
    aconv encoded_jobs captured.case10173_complete_encoded_jobs in
  candle_q_dim_analytic_jet_profile_event
    "shared-root-identity-check-end";
  let axioms_after = axioms () in
  if length roots <> 3305 || length encoded_cells <> 4173 ||
     not identical ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case10173 shared-root encoding: validation failed";
  print_endline
    "CANDLE_CV_CASE10173_SHARED_ROOT_ENCODING_OK DEVELOPMENT_NON_RELEASE roots=3305 cells=4173 identical=1 assumptions=0 axiom_growth=0";;

end;;
