(* Refine only the failing child or children of the best measured first split. *)

needs "candle/test_cv_compute_analytic_expr_disjunctive_third_sibling_batch_remaining_scan.ml";;

module Test_cv_compute_analytic_expr_disjunctive_third_sibling_batch_depth2_scan = struct

open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;
open Test_cv_compute_analytic_expr_disjunctive_third_sibling_batch_axis1_scan;;
open Test_cv_compute_analytic_expr_disjunctive_third_sibling_batch_remaining_scan;;

let candle_disjunctive_third_batch_one_level_candidates =
  candle_disjunctive_third_batch_axis1_candidates @
  candle_disjunctive_third_batch_remaining_candidates;;
let candle_disjunctive_third_batch_one_level_rejected =
  candle_disjunctive_third_batch_axis1_rejected @
  candle_disjunctive_third_batch_remaining_rejected;;

let candle_disjunctive_third_batch_one_level_child
    record index selected axis side =
  try
    List.find
      (fun (actual_record,actual_index,actual_selected,actual_axis,
            actual_side,_) ->
        actual_record = record && actual_index = index &&
        actual_selected = selected && actual_axis = axis &&
        actual_side = side)
      candle_disjunctive_third_batch_one_level_candidates
  with Not_found ->
    failwith "third sibling depth2 scan: first child missing";;

let candle_disjunctive_third_batch_one_level_child_failed
    record index selected axis side =
  List.exists
    (fun (actual_record,actual_index,actual_selected,actual_axis,
          actual_side,_) ->
      actual_record = record && actual_index = index &&
      actual_selected = selected && actual_axis = axis &&
      actual_side = side)
    candle_disjunctive_third_batch_one_level_rejected;;

let candle_disjunctive_third_batch_one_level_failure_count
    record index selected axis =
  (if candle_disjunctive_third_batch_one_level_child_failed
        record index selected axis 0 then 1 else 0) +
  (if candle_disjunctive_third_batch_one_level_child_failed
        record index selected axis 1 then 1 else 0);;

let candle_disjunctive_third_batch_choose_first_axis
    record index selected =
  let rec choose best_axis best_failures = function
    | [] -> best_axis
    | axis::remaining ->
        let failures =
          candle_disjunctive_third_batch_one_level_failure_count
            record index selected axis in
        if failures < best_failures
        then choose axis failures remaining
        else choose best_axis best_failures remaining in
  let first_failures =
    candle_disjunctive_third_batch_one_level_failure_count
      record index selected 1 in
  choose 1 first_failures [2;3;4;5;6];;

let candle_disjunctive_third_batch_depth2_first_plans =
  map
    (fun (record,index,selected) ->
      record,index,selected,
      candle_disjunctive_third_batch_choose_first_axis
        record index selected)
    candle_disjunctive_third_batch_remaining_unsolved;;

let candle_disjunctive_third_batch_failed_first_children_for
    record index selected axis =
  let rec collect side =
    if side > 1 then []
    else
      let (_,_,_,_,_,domain) =
        candle_disjunctive_third_batch_one_level_child
          record index selected axis side in
      let remaining = collect (side + 1) in
      if candle_disjunctive_third_batch_one_level_child_failed
           record index selected axis side
      then (record,index,selected,axis,side,domain)::remaining
      else remaining in
  collect 0;;

let candle_disjunctive_third_batch_failed_first_children =
  List.flatten
    (map
      (fun (record,index,selected,axis) ->
        candle_disjunctive_third_batch_failed_first_children_for
          record index selected axis)
      candle_disjunctive_third_batch_depth2_first_plans);;

let candle_disjunctive_third_batch_grandchildren_for
    record index selected first_axis first_side domain =
  let rec collect axis =
    if axis > 6 then []
    else
      let left,right = M_verifier.split_domain 6 6 axis domain in
      (record,index,selected,first_axis,first_side,axis,0,left)::
      (record,index,selected,first_axis,first_side,axis,1,right)::
      collect (axis + 1) in
  collect 1;;

let candle_disjunctive_third_batch_depth2_candidates =
  List.flatten
    (map
      (fun (record,index,selected,first_axis,first_side,domain) ->
        candle_disjunctive_third_batch_grandchildren_for
          record index selected first_axis first_side domain)
      candle_disjunctive_third_batch_failed_first_children);;
let candle_disjunctive_third_batch_depth2_function0 =
  List.filter
    (fun (_,_,selected,_,_,_,_,_) -> selected = 0)
    candle_disjunctive_third_batch_depth2_candidates;;
let candle_disjunctive_third_batch_depth2_function1 =
  List.filter
    (fun (_,_,selected,_,_,_,_,_) -> selected = 1)
    candle_disjunctive_third_batch_depth2_candidates;;

let candle_disjunctive_third_batch_depth2_jobs candidates =
  map
    (fun (record,index,selected,_,_,_,_,domain) ->
      record,index,selected,domain)
    candidates;;

let candle_disjunctive_third_batch_depth2_scan_failures
    label prepared point_plan candidates =
  if candidates = [] then []
  else
    snd
      (candle_disjunctive_next_batch_scan_run label prepared point_plan
        (candle_disjunctive_third_batch_depth2_jobs candidates));;

let candle_disjunctive_third_batch_depth2_axioms_before = axioms ();;
let candle_disjunctive_third_batch_depth2_function0_failures =
  candle_disjunctive_third_batch_depth2_scan_failures
    "third-sibling-batch-function0-depth2-scan"
    candle_disjunctive_next_batch_prepared0
    candle_disjunctive_next_batch_point_plan0
    candle_disjunctive_third_batch_depth2_function0;;
let candle_disjunctive_third_batch_depth2_function1_failures =
  candle_disjunctive_third_batch_depth2_scan_failures
    "third-sibling-batch-function1-depth2-scan"
    candle_disjunctive_next_batch_prepared1
    candle_disjunctive_next_batch_point_plan1
    candle_disjunctive_third_batch_depth2_function1;;

let candle_disjunctive_third_batch_depth2_rejected =
  candle_disjunctive_next_batch_select_failures 0
    candle_disjunctive_third_batch_depth2_function0_failures
    candle_disjunctive_third_batch_depth2_function0 @
  candle_disjunctive_next_batch_select_failures 0
    candle_disjunctive_third_batch_depth2_function1_failures
    candle_disjunctive_third_batch_depth2_function1;;

let candle_disjunctive_third_batch_depth2_child_failed
    record index selected first_axis first_side axis side =
  List.exists
    (fun (actual_record,actual_index,actual_selected,actual_first_axis,
          actual_first_side,actual_axis,actual_side,_) ->
      actual_record = record && actual_index = index &&
      actual_selected = selected && actual_first_axis = first_axis &&
      actual_first_side = first_side && actual_axis = axis &&
      actual_side = side)
    candle_disjunctive_third_batch_depth2_rejected;;

let candle_disjunctive_third_batch_depth2_choose_axis
    record index selected first_axis first_side =
  try
    Some
      (List.find
        (fun axis ->
          not
            (candle_disjunctive_third_batch_depth2_child_failed
              record index selected first_axis first_side axis 0) &&
          not
            (candle_disjunctive_third_batch_depth2_child_failed
              record index selected first_axis first_side axis 1))
        [1;2;3;4;5;6])
  with Not_found -> None;;

let rec candle_disjunctive_third_batch_depth2_select = function
  | [] -> [],[]
  | (record,index,selected,first_axis,first_side,_)::remaining ->
      let choices,unsolved =
        candle_disjunctive_third_batch_depth2_select remaining in
      (match candle_disjunctive_third_batch_depth2_choose_axis
               record index selected first_axis first_side with
       | Some axis ->
           (record,index,selected,first_axis,first_side,axis)::choices,
           unsolved
       | None ->
           choices,
           (record,index,selected,first_axis,first_side)::unsolved);;

let candle_disjunctive_third_batch_depth2_selected,
    candle_disjunctive_third_batch_depth2_unsolved =
  candle_disjunctive_third_batch_depth2_select
    candle_disjunctive_third_batch_failed_first_children;;

let rec candle_disjunctive_third_batch_depth2_first_string = function
  | [] -> ""
  | [(record,index,selected,axis)] ->
      string_of_int record ^ ":" ^ string_of_int index ^ ":" ^
      string_of_int selected ^ ":" ^ string_of_int axis
  | (record,index,selected,axis)::remaining ->
      string_of_int record ^ ":" ^ string_of_int index ^ ":" ^
      string_of_int selected ^ ":" ^ string_of_int axis ^ "," ^
      candle_disjunctive_third_batch_depth2_first_string remaining;;

let rec candle_disjunctive_third_batch_depth2_selection_string = function
  | [] -> ""
  | [(record,index,selected,first_axis,first_side,axis)] ->
      string_of_int record ^ ":" ^ string_of_int index ^ ":" ^
      string_of_int selected ^ ":" ^ string_of_int first_axis ^ ":" ^
      string_of_int first_side ^ ":" ^ string_of_int axis
  | (record,index,selected,first_axis,first_side,axis)::remaining ->
      string_of_int record ^ ":" ^ string_of_int index ^ ":" ^
      string_of_int selected ^ ":" ^ string_of_int first_axis ^ ":" ^
      string_of_int first_side ^ ":" ^ string_of_int axis ^ "," ^
      candle_disjunctive_third_batch_depth2_selection_string remaining;;

let rec candle_disjunctive_third_batch_depth2_unsolved_string = function
  | [] -> ""
  | [(record,index,selected,first_axis,first_side)] ->
      string_of_int record ^ ":" ^ string_of_int index ^ ":" ^
      string_of_int selected ^ ":" ^ string_of_int first_axis ^ ":" ^
      string_of_int first_side
  | (record,index,selected,first_axis,first_side)::remaining ->
      string_of_int record ^ ":" ^ string_of_int index ^ ":" ^
      string_of_int selected ^ ":" ^ string_of_int first_axis ^ ":" ^
      string_of_int first_side ^ "," ^
      candle_disjunctive_third_batch_depth2_unsolved_string remaining;;

let candle_disjunctive_third_batch_depth2_axioms_after = axioms ();;
let candle_disjunctive_third_batch_depth2_expected =
  12 * length candle_disjunctive_third_batch_failed_first_children;;

if length candle_disjunctive_third_batch_remaining_unsolved <> 17 ||
   length candle_disjunctive_third_batch_depth2_first_plans <> 17 ||
   length candle_disjunctive_third_batch_failed_first_children < 17 ||
   length candle_disjunctive_third_batch_failed_first_children > 34 ||
   length candle_disjunctive_third_batch_depth2_candidates <>
     candle_disjunctive_third_batch_depth2_expected ||
   length candle_disjunctive_third_batch_depth2_function0 +
     length candle_disjunctive_third_batch_depth2_function1 <>
     candle_disjunctive_third_batch_depth2_expected ||
   length candle_disjunctive_third_batch_depth2_selected +
     length candle_disjunctive_third_batch_depth2_unsolved <>
     length candle_disjunctive_third_batch_failed_first_children ||
   length candle_disjunctive_third_batch_depth2_axioms_after <>
     length candle_disjunctive_third_batch_depth2_axioms_before ||
   not
     (List.for_all
       (fun axiom ->
         List.mem axiom candle_disjunctive_third_batch_depth2_axioms_before)
       candle_disjunctive_third_batch_depth2_axioms_after) then
  failwith "third sibling depth2 scan: validation failed";;

print_endline
  ("CANDLE_CV_THIRD_SIBLING_BATCH_DEPTH2_SCAN_OK DEVELOPMENT_NON_RELEASE" ^
   " unresolved_source_leaves=" ^
   string_of_int
     (length candle_disjunctive_third_batch_remaining_unsolved) ^
   " first_splits=" ^
   candle_disjunctive_third_batch_depth2_first_string
     candle_disjunctive_third_batch_depth2_first_plans ^
   " failed_first_children=" ^
   string_of_int
     (length candle_disjunctive_third_batch_failed_first_children) ^
   " candidate_grandchildren=" ^
   string_of_int candle_disjunctive_third_batch_depth2_expected ^
   " rejected_grandchildren=" ^
   string_of_int (length candle_disjunctive_third_batch_depth2_rejected) ^
   " selected_second_splits=" ^
   candle_disjunctive_third_batch_depth2_selection_string
     candle_disjunctive_third_batch_depth2_selected ^
   " unsolved=" ^
   candle_disjunctive_third_batch_depth2_unsolved_string
     candle_disjunctive_third_batch_depth2_unsolved ^
   " assumptions=0 axiom_growth=0");;

end;;
