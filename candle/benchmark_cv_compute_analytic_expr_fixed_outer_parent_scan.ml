(* ========================================================================== *)
(* Batched fixed-outer parent/one-split scan for untrusted forest planning.  *)
(*                                                                            *)
(* A configuration fragment supplies a label and strictly increasing parent  *)
(* indices.  Each result contains the parent verdict followed by left/right  *)
(* verdicts for axes one through six.  A proof-producing replay must validate *)
(* every selected cell; these flags carry no theorem authority.              *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_flags.ml";;
needs "candle/cv_compute_analytic_expr_action296_fixed_outer_grouped_forest_prove.ml";;
needs "candle/cv_compute_analytic_expr_stable_program_data.ml";;

open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_flags;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_action296_adaptive_forest_prove;;
open Candle_cv_action296_stable_grouped_forest_prove;;

let candle_fixed_outer_parent_scan_axioms_before = axioms ();;

let candle_fixed_outer_parent_scan_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=fixed-outer-parent-scan" ^
     " scope=parents phase=" ^ phase ^ " event=" ^ event);;

let rec candle_fixed_outer_parent_scan_strict previous = function
  | [] -> true
  | index :: remaining ->
      index > previous && index >= 0 &&
      index < length !candle_action296_leaf_grouping_leaves &&
      candle_fixed_outer_parent_scan_strict index remaining;;

if candle_fixed_outer_parent_scan_indices = [] ||
   not
     (candle_fixed_outer_parent_scan_strict
       (-1) candle_fixed_outer_parent_scan_indices) then
  failwith "fixed outer parent scan: invalid configured indices";;

let candle_fixed_outer_parent_scan_children parent =
  List.flatten
    (map
      (fun axis ->
        let left,right =
          M_verifier.split_domain
            candle_action296_plan_dimension 6 axis parent in
        [left;right])
      [1;2;3;4;5;6]);;

let candle_fixed_outer_parent_scan_encode_cell point_plan domain =
  let cell = candle_action296_stable_group_cell point_plan domain in
  let boxes =
    candle_poly_fixture_q_boxes
      cell.stable_batch_lower cell.stable_batch_upper in
  candle_q_dim_stable_program_cval_pair
    (candle_q_dim_stable_program_encode_intervals
      cell.stable_batch_center_intervals)
    (candle_q_dim_stable_program_encode_intervals (dest_list boxes));;

let candle_fixed_outer_parent_scan_task point_plan index =
  let parent = List.nth !candle_action296_leaf_grouping_leaves index in
  let lower,upper = candle_action296_leaf_grouping_domain_bounds parent in
  let box_intervals =
    candle_action296_stable_group_box_intervals point_plan lower upper in
  let domains =
    if candle_fixed_outer_parent_scan_include_children then
      parent :: candle_fixed_outer_parent_scan_children parent
    else [parent] in
  let jobs =
    map (candle_fixed_outer_parent_scan_encode_cell point_plan) domains in
  candle_q_dim_stable_program_cval_pair
    (candle_q_dim_stable_program_encode_intervals box_intervals)
    (candle_q_dim_stable_program_cval_list jobs);;

let rec candle_fixed_outer_parent_scan_dest_list context value =
  if aconv value `Cexp_num 0` then [] else
  let operator,arguments = strip_comb value in
  if aconv operator `Cexp_pair` then
    match arguments with
    | [head;tail] ->
        head :: candle_fixed_outer_parent_scan_dest_list context tail
    | _ -> failwith (context ^ ": malformed pair")
  else failwith (context ^ ": expected encoded list");;

let candle_fixed_outer_parent_scan_flag flag =
  if aconv flag `Cexp_num 1` then "1"
  else if aconv flag `Cexp_num 0` then "0"
  else failwith "fixed outer parent scan: non-Boolean flag";;

let _ =
  candle_fixed_outer_parent_scan_marker "data-preparation" "begin";;
let candle_fixed_outer_parent_scan_point_plan =
  candle_action296_forest_point_plan;;
let candle_fixed_outer_parent_scan_tasks =
  map
    (candle_fixed_outer_parent_scan_task
      candle_fixed_outer_parent_scan_point_plan)
    candle_fixed_outer_parent_scan_indices;;
let candle_fixed_outer_parent_scan_tasks_term =
  candle_q_dim_stable_program_cval_list
    candle_fixed_outer_parent_scan_tasks;;
let _ =
  candle_fixed_outer_parent_scan_marker "data-preparation" "end";;

let candle_fixed_outer_parent_scan_call =
  list_mk_comb
    (`candle_cv_fso_stable_task_flags`,
     [candle_action296_plan_prepared.program_representation_term;
      candle_fixed_outer_parent_scan_tasks_term]);;

let _ = candle_fixed_outer_parent_scan_marker "kernel-compute" "begin";;
let candle_fixed_outer_parent_scan_theorem =
  candle_q_dim_analytic_jet_compute
    candle_cv_fso_flags_compute_eqs candle_fixed_outer_parent_scan_call;;
let _ = candle_fixed_outer_parent_scan_marker "kernel-compute" "end";;

if hyp candle_fixed_outer_parent_scan_theorem <> [] then
  failwith "fixed outer parent scan: computed theorem assumptions";;

let candle_fixed_outer_parent_scan_flag_groups =
  map
    (candle_fixed_outer_parent_scan_dest_list
      "fixed outer parent scan flags")
    (candle_fixed_outer_parent_scan_dest_list
      "fixed outer parent scan tasks"
      (rand (concl candle_fixed_outer_parent_scan_theorem)));;

let rec candle_fixed_outer_parent_scan_print indices groups =
  match indices,groups with
  | [],[] -> ()
  | index :: remaining_indices,flags :: remaining_groups ->
      let expected =
        if candle_fixed_outer_parent_scan_include_children then 13 else 1 in
      if length flags <> expected then
        failwith "fixed outer parent scan: flag cardinality";
      print_endline
        ("CANDLE_CV_FIXED_OUTER_PARENT_SCAN_ROOT" ^
         " label=" ^ candle_fixed_outer_parent_scan_label ^
         " index=" ^ string_of_int index ^
         " flags=" ^
         String.concat "," (map candle_fixed_outer_parent_scan_flag flags));
      candle_fixed_outer_parent_scan_print
        remaining_indices remaining_groups
  | _ -> failwith "fixed outer parent scan: result cardinality";;

let _ =
  candle_fixed_outer_parent_scan_print
    candle_fixed_outer_parent_scan_indices
    candle_fixed_outer_parent_scan_flag_groups;;

let candle_fixed_outer_parent_scan_axioms_after = axioms ();;
if length candle_fixed_outer_parent_scan_axioms_after <>
     length candle_fixed_outer_parent_scan_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_fixed_outer_parent_scan_axioms_before)
       candle_fixed_outer_parent_scan_axioms_after) then
  failwith "fixed outer parent scan: axiom set changed";;

print_endline
  ("CANDLE_CV_FIXED_OUTER_PARENT_SCAN_RESULT label=" ^
   candle_fixed_outer_parent_scan_label ^
   " roots=" ^
   string_of_int (length candle_fixed_outer_parent_scan_indices) ^
   " verdicts=" ^
   string_of_int
     ((if candle_fixed_outer_parent_scan_include_children then 13 else 1) *
      length candle_fixed_outer_parent_scan_indices) ^
   " theorem_authority=none");;
print_endline
  "CANDLE_CV_FIXED_OUTER_PARENT_SCAN_OK DEVELOPMENT_NON_RELEASE";;
