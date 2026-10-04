(* Count maximal same-function subtrees in the authentic mixed certificate. *)

needs "candle/cv_compute_analytic_expr_disjunctive_next_sibling_batch.ml";;

module Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_topology = struct

open Certificate;;
open Candle_cv_analytic_expr_disjunctive_next_sibling_batch;;

let rec candle_disjunctive_next_batch_topology_analyze = function
  | P_result_pass (_,selected,raw_flag) ->
      if selected < 0 || selected > 1 || raw_flag then
        failwith "next sibling topology: pass selection drift";
      Some selected,1,[selected,1]
  | P_result_glue (_,_,convex_flag,left,right) ->
      if convex_flag then failwith "next sibling topology: convex node";
      let left_selection,left_leaves,left_groups =
        candle_disjunctive_next_batch_topology_analyze left in
      let right_selection,right_leaves,right_groups =
        candle_disjunctive_next_batch_topology_analyze right in
      let leaves = left_leaves + right_leaves in
      (match left_selection,right_selection with
       | Some left_function,Some right_function
           when left_function = right_function ->
           Some left_function,leaves,[left_function,leaves]
       | _ -> None,leaves,left_groups @ right_groups)
  | P_result_mono _ ->
      failwith "next sibling topology: monotonicity node"
  | P_result_ref _ ->
      failwith "next sibling topology: reference node";;

let candle_disjunctive_next_batch_topology_summary expected tree =
  let _,leaves,groups =
    candle_disjunctive_next_batch_topology_analyze tree in
  let function0 =
    length (List.filter (fun (selected,_) -> selected = 0) groups) in
  let function1 =
    length (List.filter (fun (selected,_) -> selected = 1) groups) in
  let maximum =
    itlist
      (fun (_,size) current -> if size > current then size else current)
      groups 0 in
  let grouped_leaves =
    itlist (fun (_,size) total -> size + total) groups 0 in
  if leaves <> expected || grouped_leaves <> expected ||
     function0 + function1 <> length groups then
    failwith "next sibling topology: component accounting drift";
  length groups,function0,function1,maximum;;

let candle_disjunctive_case16617_component_count,
    candle_disjunctive_case16617_function0_components,
    candle_disjunctive_case16617_function1_components,
    candle_disjunctive_case16617_maximum_component =
  candle_disjunctive_next_batch_topology_summary
    candle_disjunctive_case16617_leaf_count
    candle_disjunctive_case16617_precision_tree;;
let candle_disjunctive_case16593_component_count,
    candle_disjunctive_case16593_function0_components,
    candle_disjunctive_case16593_function1_components,
    candle_disjunctive_case16593_maximum_component =
  candle_disjunctive_next_batch_topology_summary
    candle_disjunctive_case16593_leaf_count
    candle_disjunctive_case16593_precision_tree;;
let candle_disjunctive_case16582_component_count,
    candle_disjunctive_case16582_function0_components,
    candle_disjunctive_case16582_function1_components,
    candle_disjunctive_case16582_maximum_component =
  candle_disjunctive_next_batch_topology_summary
    candle_disjunctive_case16582_leaf_count
    candle_disjunctive_case16582_precision_tree;;

print_endline
  ("CANDLE_CV_NEXT_SIBLING_BATCH_TOPOLOGY_OK DEVELOPMENT_NON_RELEASE" ^
   " record16617_components=" ^
   string_of_int candle_disjunctive_case16617_component_count ^
   " function0=0 function1=" ^
   string_of_int candle_disjunctive_case16617_function1_components ^
   " maximum=" ^
   string_of_int candle_disjunctive_case16617_maximum_component ^
   " record16593_components=" ^
   string_of_int candle_disjunctive_case16593_component_count ^
   " function0=0 function1=" ^
   string_of_int candle_disjunctive_case16593_function1_components ^
   " maximum=" ^
   string_of_int candle_disjunctive_case16593_maximum_component ^
   " record16582_components=" ^
   string_of_int candle_disjunctive_case16582_component_count ^
   " function0=" ^
   string_of_int candle_disjunctive_case16582_function0_components ^
   " function1=" ^
   string_of_int candle_disjunctive_case16582_function1_components ^
   " maximum=" ^
   string_of_int candle_disjunctive_case16582_maximum_component);;

end;;
