(* ========================================================================== *)
(* Batched fixed-outer depth-two branch scan for untrusted forest planning.  *)
(*                                                                            *)
(* A configuration fragment supplies (root index, first axis, branch) work.  *)
(* Each result reports the twelve one-split verdicts below that branch.       *)
(* The enclosing original root supplies the fixed outer box, matching the    *)
(* conservative context used by the parent scanner.  These flags carry no    *)
(* theorem authority; the proof-producing forest replay remains decisive.    *)
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

let candle_fixed_outer_depth2_scan_axioms_before = axioms ();;

let candle_fixed_outer_depth2_scan_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=fixed-outer-depth2-scan" ^
     " scope=branches phase=" ^ phase ^ " event=" ^ event);;

let candle_fixed_outer_depth2_scan_work_before
    (left_index,left_axis,left_branch)
    (right_index,right_axis,right_branch) =
  left_index < right_index ||
  (left_index = right_index &&
   (left_axis < right_axis ||
    (left_axis = right_axis && left_branch < right_branch)));;

let candle_fixed_outer_depth2_scan_valid_item (index,axis,branch) =
  index >= 0 && index < length !candle_action296_leaf_grouping_leaves &&
  axis >= 1 && axis <= 6 && (branch = 0 || branch = 1);;

let rec candle_fixed_outer_depth2_scan_strict previous = function
  | [] -> true
  | item :: remaining ->
      candle_fixed_outer_depth2_scan_valid_item item &&
      (match previous with
       | None -> true
       | Some preceding ->
           candle_fixed_outer_depth2_scan_work_before preceding item) &&
      candle_fixed_outer_depth2_scan_strict (Some item) remaining;;

if candle_fixed_outer_depth2_scan_work = [] ||
   not (candle_fixed_outer_depth2_scan_strict
         None candle_fixed_outer_depth2_scan_work) then
  failwith "fixed outer depth2 scan: invalid configured work";;

let candle_fixed_outer_depth2_scan_children parent =
  List.flatten
    (map
      (fun axis ->
        let left,right =
          M_verifier.split_domain
            candle_action296_plan_dimension 6 axis parent in
        [left;right])
      [1;2;3;4;5;6]);;

let candle_fixed_outer_depth2_scan_encode_cell point_plan domain =
  let cell = candle_action296_stable_group_cell point_plan domain in
  let boxes =
    candle_poly_fixture_q_boxes
      cell.stable_batch_lower cell.stable_batch_upper in
  candle_q_dim_stable_program_cval_pair
    (candle_q_dim_stable_program_encode_intervals
      cell.stable_batch_center_intervals)
    (candle_q_dim_stable_program_encode_intervals (dest_list boxes));;

let candle_fixed_outer_depth2_scan_branch_domain parent axis branch =
  let left,right =
    M_verifier.split_domain candle_action296_plan_dimension 6 axis parent in
  if branch = 0 then left else right;;

let candle_fixed_outer_depth2_scan_task point_plan (index,axis,branch) =
  let parent = List.nth !candle_action296_leaf_grouping_leaves index in
  let lower,upper = candle_action296_leaf_grouping_domain_bounds parent in
  let box_intervals =
    candle_action296_stable_group_box_intervals point_plan lower upper in
  let branch_domain =
    candle_fixed_outer_depth2_scan_branch_domain parent axis branch in
  let jobs =
    map
      (candle_fixed_outer_depth2_scan_encode_cell point_plan)
      (candle_fixed_outer_depth2_scan_children branch_domain) in
  candle_q_dim_stable_program_cval_pair
    (candle_q_dim_stable_program_encode_intervals box_intervals)
    (candle_q_dim_stable_program_cval_list jobs);;

let rec candle_fixed_outer_depth2_scan_dest_list context value =
  if aconv value `Cexp_num 0` then [] else
  let operator,arguments = strip_comb value in
  if aconv operator `Cexp_pair` then
    match arguments with
    | [head;tail] ->
        head :: candle_fixed_outer_depth2_scan_dest_list context tail
    | _ -> failwith (context ^ ": malformed pair")
  else failwith (context ^ ": expected encoded list");;

let candle_fixed_outer_depth2_scan_flag flag =
  if aconv flag `Cexp_num 1` then "1"
  else if aconv flag `Cexp_num 0` then "0"
  else failwith "fixed outer depth2 scan: non-Boolean flag";;

let _ = candle_fixed_outer_depth2_scan_marker "data-preparation" "begin";;
let candle_fixed_outer_depth2_scan_point_plan =
  candle_action296_forest_point_plan;;
let candle_fixed_outer_depth2_scan_tasks =
  map
    (candle_fixed_outer_depth2_scan_task
      candle_fixed_outer_depth2_scan_point_plan)
    candle_fixed_outer_depth2_scan_work;;
let candle_fixed_outer_depth2_scan_tasks_term =
  candle_q_dim_stable_program_cval_list
    candle_fixed_outer_depth2_scan_tasks;;
let _ = candle_fixed_outer_depth2_scan_marker "data-preparation" "end";;

let candle_fixed_outer_depth2_scan_call =
  list_mk_comb
    (`candle_cv_fso_stable_task_flags`,
     [candle_action296_plan_prepared.program_representation_term;
      candle_fixed_outer_depth2_scan_tasks_term]);;

let _ = candle_fixed_outer_depth2_scan_marker "kernel-compute" "begin";;
let candle_fixed_outer_depth2_scan_theorem =
  candle_q_dim_analytic_jet_compute
    candle_cv_fso_flags_compute_eqs candle_fixed_outer_depth2_scan_call;;
let _ = candle_fixed_outer_depth2_scan_marker "kernel-compute" "end";;

if hyp candle_fixed_outer_depth2_scan_theorem <> [] then
  failwith "fixed outer depth2 scan: computed theorem assumptions";;

let candle_fixed_outer_depth2_scan_flag_groups =
  map
    (candle_fixed_outer_depth2_scan_dest_list
      "fixed outer depth2 scan flags")
    (candle_fixed_outer_depth2_scan_dest_list
      "fixed outer depth2 scan tasks"
      (rand (concl candle_fixed_outer_depth2_scan_theorem)));;

let rec candle_fixed_outer_depth2_scan_print work groups =
  match work,groups with
  | [],[] -> ()
  | (index,axis,branch) :: remaining_work,
    flags :: remaining_groups ->
      if length flags <> 12 then
        failwith "fixed outer depth2 scan: flag cardinality";
      print_endline
        ("CANDLE_CV_FIXED_OUTER_DEPTH2_SCAN_BRANCH" ^
         " label=" ^ candle_fixed_outer_depth2_scan_label ^
         " index=" ^ string_of_int index ^
         " first_axis=" ^ string_of_int axis ^
         " branch=" ^ string_of_int branch ^
         " flags=" ^
         String.concat "," (map candle_fixed_outer_depth2_scan_flag flags));
      candle_fixed_outer_depth2_scan_print remaining_work remaining_groups
  | _ -> failwith "fixed outer depth2 scan: result cardinality";;

let _ =
  candle_fixed_outer_depth2_scan_print
    candle_fixed_outer_depth2_scan_work
    candle_fixed_outer_depth2_scan_flag_groups;;

let candle_fixed_outer_depth2_scan_axioms_after = axioms ();;
if length candle_fixed_outer_depth2_scan_axioms_after <>
     length candle_fixed_outer_depth2_scan_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_fixed_outer_depth2_scan_axioms_before)
       candle_fixed_outer_depth2_scan_axioms_after) then
  failwith "fixed outer depth2 scan: axiom set changed";;

print_endline
  ("CANDLE_CV_FIXED_OUTER_DEPTH2_SCAN_RESULT label=" ^
   candle_fixed_outer_depth2_scan_label ^
   " branches=" ^
   string_of_int (length candle_fixed_outer_depth2_scan_work) ^
   " verdicts=" ^
   string_of_int (12 * length candle_fixed_outer_depth2_scan_work) ^
   " theorem_authority=none");;
print_endline
  "CANDLE_CV_FIXED_OUTER_DEPTH2_SCAN_OK DEVELOPMENT_NON_RELEASE";;
