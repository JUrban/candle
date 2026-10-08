(* Refine only the failed children of the best measured first split.         *)
(* DEVELOPMENT / NON-RELEASE.  This is untrusted plan discovery; the final *)
(* theorem-producing complete checker remains the acceptance boundary.      *)

needs "candle/test_cv_compute_analytic_expr_disjunctive_fifth_sibling_batch_remaining_scan.ml";;

module Test_cv_compute_analytic_expr_disjunctive_fifth_sibling_batch_depth2_scan = struct

open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;
open Test_cv_compute_analytic_expr_disjunctive_fifth_sibling_batch_axis1_scan;;
open Test_cv_compute_analytic_expr_disjunctive_fifth_sibling_batch_remaining_scan;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_scan;;

let candle_disjunctive_fifth_batch_depth2_first_plans_get,
    candle_disjunctive_fifth_batch_failed_first_children_get,
    candle_disjunctive_fifth_batch_depth2_candidates_get,
    candle_disjunctive_fifth_batch_depth2_rejected_get,
    candle_disjunctive_fifth_batch_depth2_selected_get,
    candle_disjunctive_fifth_batch_depth2_unsolved_get =
  let one_level_candidates =
    candle_disjunctive_fifth_batch_axis1_candidates_get () @
    candle_disjunctive_fifth_batch_remaining_candidates_get ()
  and one_level_rejected =
    candle_disjunctive_fifth_batch_axis1_rejected_get () @
    candle_disjunctive_fifth_batch_remaining_rejected_get ()
  and unresolved =
    candle_disjunctive_fifth_batch_remaining_unsolved_get () in
  let one_level_child record index selected axis side =
    try
      List.find
        (fun (actual_record,actual_index,actual_selected,actual_axis,
              actual_side,_) ->
          actual_record = record && actual_index = index &&
          actual_selected = selected && actual_axis = axis &&
          actual_side = side)
        one_level_candidates
    with Not_found ->
      failwith "fifth sibling depth2 scan: first child missing" in
  let one_level_child_failed record index selected axis side =
    List.exists
      (fun (actual_record,actual_index,actual_selected,actual_axis,
            actual_side,_) ->
        actual_record = record && actual_index = index &&
        actual_selected = selected && actual_axis = axis &&
        actual_side = side)
      one_level_rejected in
  let one_level_failure_count record index selected axis =
    (if one_level_child_failed record index selected axis 0 then 1 else 0) +
    (if one_level_child_failed record index selected axis 1 then 1 else 0) in
  let choose_first_axis record index selected =
    let rec choose best_axis best_failures = function
      | [] -> best_axis
      | axis::remaining ->
          let failures =
            one_level_failure_count record index selected axis in
          if failures < best_failures
          then choose axis failures remaining
          else choose best_axis best_failures remaining in
    choose 1 (one_level_failure_count record index selected 1) [2;3;4;5;6] in
  let first_plans =
    map
      (fun (record,index,selected) ->
        record,index,selected,choose_first_axis record index selected)
      unresolved in
  let failed_first_children_for record index selected axis =
    let rec collect side =
      if side > 1 then []
      else
        let _,_,_,_,_,domain =
          one_level_child record index selected axis side in
        let remaining = collect (side + 1) in
        if one_level_child_failed record index selected axis side
        then (record,index,selected,axis,side,domain)::remaining
        else remaining in
    collect 0 in
  let failed_first_children =
    List.flatten
      (map
        (fun (record,index,selected,axis) ->
          failed_first_children_for record index selected axis)
        first_plans) in
  let grandchildren_for
      record index selected first_axis first_side domain =
    let rec collect axis =
      if axis > 6 then []
      else
        let left,right = M_verifier.split_domain 6 6 axis domain in
        (record,index,selected,first_axis,first_side,axis,0,left)::
        (record,index,selected,first_axis,first_side,axis,1,right)::
        collect (axis + 1) in
    collect 1 in
  let candidates =
    List.flatten
      (map
        (fun (record,index,selected,first_axis,first_side,domain) ->
          grandchildren_for
            record index selected first_axis first_side domain)
        failed_first_children) in
  let function0 =
    List.filter (fun (_,_,selected,_,_,_,_,_) -> selected = 0) candidates
  and function1 =
    List.filter (fun (_,_,selected,_,_,_,_,_) -> selected = 1) candidates in
  let scan_jobs label prepared point_plan candidates =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_scan_jobs_chunked_six
      label 128 prepared
      (fun (_,_,_,_,_,_,_,domain) ->
        candle_disjunctive_next_batch_scan_cell point_plan domain)
      candidates in
  let axioms_before = axioms () in
  let count0,failures0 =
    scan_jobs
      "fifth-sibling-batch-function0-depth2-fixed-nonlinear-scan"
      candle_disjunctive_next_batch_prepared0
      candle_disjunctive_next_batch_point_plan0 function0 in
  let count1,failures1 =
    scan_jobs
      "fifth-sibling-batch-function1-depth2-fixed-nonlinear-scan"
      candle_disjunctive_next_batch_prepared1
      candle_disjunctive_next_batch_point_plan1 function1 in
  let rejected =
    candle_disjunctive_next_batch_select_failures 0 failures0 function0 @
    candle_disjunctive_next_batch_select_failures 0 failures1 function1 in
  let child_failed
      record index selected first_axis first_side axis side =
    List.exists
      (fun (actual_record,actual_index,actual_selected,actual_first_axis,
            actual_first_side,actual_axis,actual_side,_) ->
        actual_record = record && actual_index = index &&
        actual_selected = selected && actual_first_axis = first_axis &&
        actual_first_side = first_side && actual_axis = axis &&
        actual_side = side)
      rejected in
  let choose_axis record index selected first_axis first_side =
    try
      Some
        (List.find
          (fun axis ->
            not
              (child_failed record index selected first_axis first_side
                axis 0) &&
            not
              (child_failed record index selected first_axis first_side
                axis 1))
          [1;2;3;4;5;6])
    with Not_found -> None in
  let rec select = function
    | [] -> [],[]
    | (record,index,selected,first_axis,first_side,_)::remaining ->
        let choices,unsolved = select remaining in
        (match choose_axis record index selected first_axis first_side with
         | Some axis ->
             (record,index,selected,first_axis,first_side,axis)::choices,
             unsolved
         | None ->
             choices,
             (record,index,selected,first_axis,first_side)::unsolved) in
  let selected,unsolved = select failed_first_children in
  let expected = 12 * length failed_first_children in
  let axioms_after = axioms () in
  if length first_plans <> length unresolved ||
     length failed_first_children < length unresolved ||
     length failed_first_children > 2 * length unresolved ||
     length candidates <> expected ||
     count0 <> length function0 || count1 <> length function1 ||
     count0 + count1 <> expected ||
     length selected + length unsolved <> length failed_first_children ||
     length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun axiom -> List.mem axiom axioms_before) axioms_after) then
    failwith "fifth sibling batch depth2 scan: validation failed";
  let rec first_string = function
    | [] -> ""
    | [(record,index,selected,axis)] ->
        string_of_int record ^ ":" ^ string_of_int index ^ ":" ^
        string_of_int selected ^ ":" ^ string_of_int axis
    | (record,index,selected,axis)::remaining ->
        string_of_int record ^ ":" ^ string_of_int index ^ ":" ^
        string_of_int selected ^ ":" ^ string_of_int axis ^ "," ^
        first_string remaining in
  let rec selection_string = function
    | [] -> ""
    | [(record,index,selected,first_axis,first_side,axis)] ->
        string_of_int record ^ ":" ^ string_of_int index ^ ":" ^
        string_of_int selected ^ ":" ^ string_of_int first_axis ^ ":" ^
        string_of_int first_side ^ ":" ^ string_of_int axis
    | (record,index,selected,first_axis,first_side,axis)::remaining ->
        string_of_int record ^ ":" ^ string_of_int index ^ ":" ^
        string_of_int selected ^ ":" ^ string_of_int first_axis ^ ":" ^
        string_of_int first_side ^ ":" ^ string_of_int axis ^ "," ^
        selection_string remaining in
  let rec unsolved_string = function
    | [] -> ""
    | [(record,index,selected,first_axis,first_side)] ->
        string_of_int record ^ ":" ^ string_of_int index ^ ":" ^
        string_of_int selected ^ ":" ^ string_of_int first_axis ^ ":" ^
        string_of_int first_side
    | (record,index,selected,first_axis,first_side)::remaining ->
        string_of_int record ^ ":" ^ string_of_int index ^ ":" ^
        string_of_int selected ^ ":" ^ string_of_int first_axis ^ ":" ^
        string_of_int first_side ^ "," ^ unsolved_string remaining in
  print_endline
    ("CANDLE_CV_FIFTH_SIBLING_BATCH_DEPTH2_FIXED_NONLINEAR_SCAN_OK" ^
     " DEVELOPMENT_NON_RELEASE" ^
     " unresolved_source_leaves=" ^ string_of_int (length unresolved) ^
     " first_splits=" ^ first_string first_plans ^
     " failed_first_children=" ^ string_of_int (length failed_first_children) ^
     " candidate_grandchildren=" ^ string_of_int expected ^
     " rejected_grandchildren=" ^ string_of_int (length rejected) ^
     " selected_second_splits=" ^ selection_string selected ^
     " unsolved=" ^ unsolved_string unsolved ^
     " assumptions=0 axiom_growth=0");
  (fun () -> first_plans),
  (fun () -> failed_first_children),
  (fun () -> candidates),
  (fun () -> rejected),
  (fun () -> selected),
  (fun () -> unsolved);;

end;;
