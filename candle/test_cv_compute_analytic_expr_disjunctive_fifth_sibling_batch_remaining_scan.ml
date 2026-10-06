(* Try axes 2--6 only for fifth-batch leaves unresolved by axis 1.          *)
(* DEVELOPMENT / NON-RELEASE.  This is untrusted plan discovery; the final *)
(* theorem-producing complete checker remains the acceptance boundary.      *)

needs "candle/test_cv_compute_analytic_expr_disjunctive_fifth_sibling_batch_axis1_scan.ml";;

module Test_cv_compute_analytic_expr_disjunctive_fifth_sibling_batch_remaining_scan = struct

open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_split_scan;;
open Test_cv_compute_analytic_expr_disjunctive_fifth_sibling_batch_scan;;
open Test_cv_compute_analytic_expr_disjunctive_fifth_sibling_batch_axis1_scan;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_scan;;

let candle_disjunctive_fifth_batch_remaining_candidates_get,
    candle_disjunctive_fifth_batch_remaining_rejected_get,
    candle_disjunctive_fifth_batch_remaining_selected_get,
    candle_disjunctive_fifth_batch_remaining_unsolved_get =
  let source_rejected = candle_disjunctive_fifth_batch_rejected_get ()
  and axis1_unsolved = candle_disjunctive_fifth_batch_axis1_unsolved_get () in
  let source record index selected =
    try
      List.find
        (fun (actual_record,actual_index,actual_selected,_) ->
          actual_record = record && actual_index = index &&
          actual_selected = selected)
        source_rejected
    with Not_found ->
      failwith "fifth sibling remaining scan: source leaf missing" in
  let candidates_for (record,index,selected) =
    let _,_,_,domain = source record index selected in
    List.flatten
      (map
        (fun axis ->
          let left,right = M_verifier.split_domain 6 6 axis domain in
          [(record,index,selected,axis,0,left);
           (record,index,selected,axis,1,right)])
        [2;3;4;5;6]) in
  let candidates = List.flatten (map candidates_for axis1_unsolved) in
  let function0 =
    List.filter (fun (_,_,selected,_,_,_) -> selected = 0) candidates
  and function1 =
    List.filter (fun (_,_,selected,_,_,_) -> selected = 1) candidates in
  let scan_cells point_plan selected =
    map
      (fun (_,_,_,domain) ->
        candle_disjunctive_next_batch_scan_cell point_plan domain)
      (candle_disjunctive_next_batch_split_jobs selected) in
  let axioms_before = axioms () in
  let count0,failures0 =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_scan_six
      "fifth-sibling-batch-function0-remaining-fixed-nonlinear-scan"
      candle_disjunctive_next_batch_prepared0
      (scan_cells candle_disjunctive_next_batch_point_plan0 function0) in
  let count1,failures1 =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_scan_six
      "fifth-sibling-batch-function1-remaining-fixed-nonlinear-scan"
      candle_disjunctive_next_batch_prepared1
      (scan_cells candle_disjunctive_next_batch_point_plan1 function1) in
  let rejected =
    candle_disjunctive_next_batch_select_failures 0 failures0 function0 @
    candle_disjunctive_next_batch_select_failures 0 failures1 function1 in
  let child_failed record index selected axis side =
    List.exists
      (fun (actual_record,actual_index,actual_selected,actual_axis,
            actual_side,_) ->
        actual_record = record && actual_index = index &&
        actual_selected = selected && actual_axis = axis &&
        actual_side = side)
      rejected in
  let choose_axis record index selected =
    try
      Some
        (List.find
          (fun axis ->
            not (child_failed record index selected axis 0) &&
            not (child_failed record index selected axis 1))
          [2;3;4;5;6])
    with Not_found -> None in
  let rec select = function
    | [] -> [],[]
    | (record,index,selected)::remaining ->
        let choices,unsolved = select remaining in
        (match choose_axis record index selected with
         | Some axis -> (record,index,selected,axis)::choices,unsolved
         | None -> choices,(record,index,selected)::unsolved) in
  let selected,unsolved = select axis1_unsolved in
  let expected = 10 * length axis1_unsolved in
  let axioms_after = axioms () in
  if length candidates <> expected ||
     count0 <> length function0 || count1 <> length function1 ||
     count0 + count1 <> expected ||
     length selected + length unsolved <> length axis1_unsolved ||
     length (candle_disjunctive_fifth_batch_axis1_selected_get ()) +
       length selected + length unsolved <> length source_rejected ||
     length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun axiom -> List.mem axiom axioms_before) axioms_after) then
    failwith "fifth sibling batch remaining scan: validation failed";
  print_endline
    ("CANDLE_CV_FIFTH_SIBLING_BATCH_REMAINING_FIXED_NONLINEAR_SCAN_OK" ^
     " DEVELOPMENT_NON_RELEASE" ^
     " unresolved_after_axis1=" ^ string_of_int (length axis1_unsolved) ^
     " candidate_children=" ^ string_of_int expected ^
     " rejected_children=" ^ string_of_int (length rejected) ^
     " selected_splits=" ^
     candle_disjunctive_next_batch_split_selection_string selected ^
     " unsolved=" ^
     candle_disjunctive_next_batch_split_unsolved_string unsolved ^
     " assumptions=0 axiom_growth=0");
  (fun () -> candidates),
  (fun () -> rejected),
  (fun () -> selected),
  (fun () -> unsolved);;

end;;
