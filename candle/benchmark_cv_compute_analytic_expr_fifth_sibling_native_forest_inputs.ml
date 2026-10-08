(* ========================================================================== *)
(* Export every function-1 node of the fifth sibling forest for a native    *)
(* adaptive-replay discriminator.                                            *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.  Internal-node cells are  *)
(* represented by their exact recorded domain bounds.  Square-root fields   *)
(* are explicit zero placeholders for a native run that must recompute every *)
(* enclosure; they are not certificates.  This creates diagnostic data only *)
(* and introduces no theorem or numerical verdict.                           *)
(* ========================================================================== *)

module Benchmark_cv_compute_analytic_expr_fifth_sibling_native_forest_inputs = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Candle_cv_analytic_expr_disjunctive_case16594_plan;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;
open Candle_cv_analytic_expr_disjunctive_next_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_fifth_sibling_batch_forest_plan;;

let candle_fifth_forest_native_input_rational term =
  Num.string_of_num (rat_of_term term);;

let candle_fifth_forest_native_input_vector terms =
  String.concat "," (map candle_fifth_forest_native_input_rational terms);;

let rec candle_fifth_forest_native_input_cval term =
  let constructor,arguments = strip_comb term in
  if aconv constructor `Cexp_num` then
    match arguments with
    | [value] -> "n" ^ Num.string_of_num (dest_numeral value)
    | _ -> failwith "fifth forest native input: malformed cval numeral"
  else if aconv constructor `Cexp_pair` then
    match arguments with
    | [left;right] ->
        "p(" ^ candle_fifth_forest_native_input_cval left ^ "," ^
        candle_fifth_forest_native_input_cval right ^ ")"
    | _ -> failwith "fifth forest native input: malformed cval pair"
  else failwith "fifth forest native input: non-cval source program";;

let rec candle_fifth_forest_native_input_program_length term =
  let constructor,arguments = strip_comb term in
  if aconv constructor `Cexp_num` then 0
  else if aconv constructor `Cexp_pair` then
    match arguments with
    | [_;tail] -> 1 + candle_fifth_forest_native_input_program_length tail
    | _ -> failwith "fifth forest native input: malformed program pair"
  else failwith "fifth forest native input: malformed program spine";;

let candle_fifth_forest_native_input_zero_certificates =
  "0:0,0:0,0:0,0:0,0:0,0:0,0:0,0:0,0:0,0:0";;

let candle_fifth_forest_native_input_emit_domain index domain =
  let lower,upper =
    candle_disjunctive_fixed_outer_domain_bounds domain in
  if length lower <> 6 || length upper <> 6 then
    failwith "fifth forest native input: domain shape drift";
  print_endline
    ("CANDLE_CV_NL_NATIVE_JOB\t16594\t" ^ string_of_int index ^ "\t" ^
     candle_fifth_forest_native_input_zero_certificates ^ "\t" ^
     candle_fifth_forest_native_input_zero_certificates ^ "\t" ^
     candle_fifth_forest_native_input_vector lower ^ "\t" ^
     candle_fifth_forest_native_input_vector upper);;

let candle_fifth_forest_native_input_emit_topology
    index component parent side depth kind axis =
  print_endline
    ("CANDLE_CV_NL_NATIVE_FOREST_NODE\t" ^ string_of_int index ^ "\t" ^
     string_of_int component ^ "\t" ^ string_of_int parent ^ "\t" ^
     string_of_int side ^ "\t" ^ string_of_int depth ^ "\t" ^ kind ^
     "\t" ^ string_of_int axis);;

let rec candle_fifth_forest_native_input_emit_shape
    component parent side depth index = function
  | Candle_disjunctive_next_batch_leaf (selected,domain,_) ->
      if selected <> 1 then
        failwith "fifth forest native input: mixed selection";
      candle_fifth_forest_native_input_emit_topology
        index component parent side depth "leaf" 0;
      candle_fifth_forest_native_input_emit_domain index domain;
      index + 1,1,0,depth
  | Candle_disjunctive_next_batch_node (axis,domain,left,right) ->
      candle_fifth_forest_native_input_emit_topology
        index component parent side depth "node" axis;
      candle_fifth_forest_native_input_emit_domain index domain;
      let after_left,left_leaves,left_nodes,left_depth =
        candle_fifth_forest_native_input_emit_shape
          component index 0 (depth + 1) (index + 1) left in
      let after_right,right_leaves,right_nodes,right_depth =
        candle_fifth_forest_native_input_emit_shape
          component index 1 (depth + 1) after_left right in
      after_right,left_leaves + right_leaves,
      1 + left_nodes + right_nodes,max left_depth right_depth;;

let rec candle_fifth_forest_native_input_emit_components index = function
  | [] -> index,0,0,0
  | component::components ->
      if component.next_batch_component_selected <> 1 then
        failwith "fifth forest native input: non-function1 component";
      let after_shape,leaves,nodes,depth =
        candle_fifth_forest_native_input_emit_shape
          component.next_batch_component_id (-1) (-1) 0 index
          component.next_batch_component_shape in
      let after_all,remaining_leaves,remaining_nodes,remaining_depth =
        candle_fifth_forest_native_input_emit_components
          after_shape components in
      after_all,leaves + remaining_leaves,nodes + remaining_nodes,
      max depth remaining_depth;;

let _ =
  let axioms_before = axioms () in
  let source_program =
    candle_disjunctive_next_batch_prepared1.program_representation_term in
  if candle_fifth_forest_native_input_program_length source_program <> 167
  then failwith "fifth forest native input: source program length drift";
  print_endline
    ("CANDLE_CV_NL_NATIVE_PROGRAM\t16594\t" ^
     candle_fifth_forest_native_input_cval source_program);
  let emitted,leaves,nodes,depth =
    candle_fifth_forest_native_input_emit_components 0
      candle_disjunctive_fifth_batch_components1 in
  let axioms_after = axioms () in
  if emitted <> 11718 || leaves <> 5869 || nodes <> 5849 ||
     length candle_disjunctive_fifth_batch_components1 <> 20 ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "fifth forest native input: validation failed";
  print_endline
    ("CANDLE_CV_FIFTH_SIBLING_NATIVE_FOREST_INPUTS_OK DEVELOPMENT_NON_RELEASE" ^
     " instructions=167 sqrt_slots=10 placeholder_certificates=zero" ^
     " components=20 nodes=11718" ^
     " leaves=5869 internal_nodes=5849 maximum_depth=" ^ string_of_int depth ^
     " assumptions=0 axiom_growth=0");;

end;;
