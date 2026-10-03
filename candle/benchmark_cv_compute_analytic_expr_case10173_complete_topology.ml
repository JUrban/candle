(* ========================================================================== *)
(* Complete genuine case-10173 topology for the one-verdict raw checker.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The precision tree and every adaptive forest *)
(* are untrusted ordinary plan data here.  The complete checker revalidates  *)
(* every leaf, exact split, consumed job, and final singleton root.           *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_variable_raw_plan.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_complete_topology = struct

open Certificate;;
open Candle_cv_analytic_expr_case10173_reused_plan;;
open Candle_cv_action296_forest_plan;;
open Benchmark_cv_compute_analytic_expr_case10173_variable_raw_plan;;

type candle_case10173_complete_token_data =
  | Candle_case10173_complete_leaf
  | Candle_case10173_complete_glue of int;;

let candle_case10173_complete_topology_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=case10173-complete-topology" ^
     " scope=plan phase=" ^ phase ^ " event=" ^ event);;

let rec candle_case10173_complete_forest_tokens
    tree reversed leaf_count glue_count =
  match tree with
  | Candle_action296_forest_tree_leaf _ ->
      Candle_case10173_complete_leaf :: reversed,
      leaf_count + 1,glue_count
  | Candle_action296_forest_tree_split (axis,left,right) ->
      let after_left,left_leaves,left_glues =
        candle_case10173_complete_forest_tokens
          left reversed leaf_count glue_count in
      let after_right,right_leaves,right_glues =
        candle_case10173_complete_forest_tokens
          right after_left left_leaves left_glues in
      Candle_case10173_complete_glue axis :: after_right,
      right_leaves,right_glues + 1;;

let rec candle_case10173_complete_precision_tokens
    tree expected roots reversed leaf_count glue_count =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 0 || raw_flag then
        failwith "case10173 complete topology: unexpected pass selection";
      (match roots with
       | root :: remaining ->
           if root.case10173_variable_raw_root_index <> expected then
             failwith "case10173 complete topology: root order drift";
           let after_root,leaves,glues =
             candle_case10173_complete_forest_tokens
               root.case10173_variable_raw_root_tree
               reversed leaf_count glue_count in
           remaining,expected + 1,after_root,leaves,glues
       | [] -> failwith "case10173 complete topology: missing root")
  | P_result_glue (_,split_index,convex_flag,left,right) ->
      if convex_flag then
        failwith "case10173 complete topology: unexpected convex branch";
      let roots_after_left,next_left,after_left,left_leaves,left_glues =
        candle_case10173_complete_precision_tokens
          left expected roots reversed leaf_count glue_count in
      let roots_after_right,next_right,after_right,right_leaves,right_glues =
        candle_case10173_complete_precision_tokens
          right next_left roots_after_left after_left left_leaves left_glues in
      roots_after_right,next_right,
      Candle_case10173_complete_glue (split_index + 1) :: after_right,
      right_leaves,right_glues + 1
  | P_result_mono _ ->
      failwith "case10173 complete topology: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "case10173 complete topology: unexpected reference node";;

let candle_case10173_complete_token_data_state :
    candle_case10173_complete_token_data list option ref = ref None;;

let _ =
  candle_case10173_complete_topology_marker "construction" "begin";
  let plan = candle_case10173_variable_raw_plan () in
  let remaining,next,reversed,leaf_count,glue_count =
    candle_case10173_complete_precision_tokens
      candle_case10173_plan_precision_tree 0
      plan.case10173_variable_raw_plan_roots [] 0 0 in
  let token_data = rev reversed in
  if remaining <> [] || next <> 3305 || leaf_count <> 4173 ||
     glue_count <> 4172 || length token_data <> 8345 ||
     length plan.case10173_variable_raw_plan_cells <> leaf_count then
    failwith "case10173 complete topology: complete shape drift";
  candle_case10173_complete_token_data_state := Some token_data;
  candle_case10173_complete_topology_marker "construction" "end";
  print_endline
    "CANDLE_CV_CASE10173_COMPLETE_TOPOLOGY_OK DEVELOPMENT_NON_RELEASE roots=3305 numerical_cells=4173 glue_items=4172 token_items=8345";;

let candle_case10173_complete_token_data () =
  match !candle_case10173_complete_token_data_state with
  | Some tokens -> tokens
  | None -> failwith "case10173 complete topology: unavailable";;

end;;
