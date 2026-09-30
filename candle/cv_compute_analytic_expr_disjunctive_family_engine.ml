(* ========================================================================== *)
(* Reusable checkpointed proof engine for one-function disjunctive families. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  A caller supplies the authenticated leaf      *)
(* order and domains.  The engine proves, validates, retains, and later       *)
(* rejoins those leaves; it does not select or trust a numerical certificate. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_disjunctive_fixed_outer_prove.ml";;

module Candle_cv_analytic_expr_disjunctive_family_engine = struct

open Certificate;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;

type candle_disjunctive_family_engine_result = {
  family_engine_leaf_index : int;
  family_engine_leaf_attempts : int;
  family_engine_leaf_proof : candle_disjunctive_fixed_outer_result;
};;

type candle_disjunctive_family_engine_state = {
  family_engine_label : string;
  family_engine_leaf_count : int;
  family_engine_function_index : int;
  family_engine_function_term : term;
  family_engine_prepared : candle_q_dim_analytic_jet_prepared_six;
  family_engine_point_plan : candle_q_dim_taylor_model_point_plan_six;
  family_engine_leaves : (int * thm) list;
  family_engine_axioms_before : thm list;
  family_engine_results : candle_disjunctive_family_engine_result list ref;
  family_engine_next_index : int ref;
  family_engine_total_attempts : int ref;
  family_engine_total_cells : int ref;
};;

let candle_disjunctive_family_engine_make
    label leaf_count function_index prepared leaves =
  if leaf_count <= 0 || length leaves <> leaf_count ||
     function_index < 0 then
    failwith "disjunctive family engine: invalid support shape";
  if not
       (List.for_all
         (fun (selected,domain) ->
           selected = function_index && hyp domain = [])
         leaves) then
    failwith "disjunctive family engine: leaf identity mismatch";
  let point_plan =
    candle_q_dim_taylor_model_point_plan_six prepared in
  if candle_disjunctive_fixed_outer_point_plan_program_count point_plan <>
       10 then
    failwith "disjunctive family engine: point-plan identity drift";
  {family_engine_label = label;
   family_engine_leaf_count = leaf_count;
   family_engine_function_index = function_index;
   family_engine_function_term =
     candle_disjunctive_fixed_outer_function_term prepared;
   family_engine_prepared = prepared;
   family_engine_point_plan = point_plan;
   family_engine_leaves = leaves;
   family_engine_axioms_before = axioms ();
   family_engine_results = ref [];
   family_engine_next_index = ref 0;
   family_engine_total_attempts = ref 0;
   family_engine_total_cells = ref 0};;

let candle_disjunctive_family_engine_validate state index domain result =
  let functions,proved_domain =
    M_verifier.dest_m_cell_list_pass
      (concl result.disjunctive_fixed_outer_theorem) in
  let expected_domain,_,_ =
    M_taylor.dest_m_cell_domain (concl domain) in
  if functions <> [state.family_engine_function_term] ||
     not (aconv proved_domain expected_domain) ||
     hyp result.disjunctive_fixed_outer_theorem <> [] then
    failwith
      ("disjunctive family engine: theorem mismatch at leaf " ^
       string_of_int index);;

let candle_disjunctive_family_engine_prove_one state index =
  if index <> !(state.family_engine_next_index) ||
     index < 0 || index >= state.family_engine_leaf_count then
    failwith "disjunctive family engine: nonsequential leaf request";
  let selected,domain = List.nth state.family_engine_leaves index in
  if selected <> state.family_engine_function_index then
    failwith "disjunctive family engine: selected function drift";
  let attempts = ref 0 in
  let result =
    candle_disjunctive_fixed_outer_prove
      state.family_engine_prepared state.family_engine_point_plan
      (state.family_engine_label ^ "-leaf-" ^ string_of_int index)
      attempts 12 domain in
  candle_disjunctive_family_engine_validate state index domain result;
  state.family_engine_results :=
    {family_engine_leaf_index = index;
     family_engine_leaf_attempts = !attempts;
     family_engine_leaf_proof = result} ::
    !(state.family_engine_results);
  state.family_engine_next_index := index + 1;
  state.family_engine_total_attempts :=
    !(state.family_engine_total_attempts) + !attempts;
  state.family_engine_total_cells :=
    !(state.family_engine_total_cells) +
    result.disjunctive_fixed_outer_cells;
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_FAMILY_ENGINE_LEAF_RESULT" ^
     " family=" ^ state.family_engine_label ^
     " leaf=" ^ string_of_int index ^
     " function=" ^ string_of_int selected ^
     " attempts=" ^ string_of_int !attempts ^
     " cells=" ^ string_of_int result.disjunctive_fixed_outer_cells ^
     " max_depth=" ^
     string_of_int result.disjunctive_fixed_outer_max_depth ^
     " theorem_digest=" ^
     Digest.to_hex
       (Digest.string
         (string_of_thm result.disjunctive_fixed_outer_theorem)));;

let candle_disjunctive_family_engine_validate_state state =
  let axioms_after = axioms () in
  if length !(state.family_engine_results) <>
       !(state.family_engine_next_index) ||
     length axioms_after <> length state.family_engine_axioms_before ||
     not
       (List.for_all
         (fun theorem ->
           List.mem theorem state.family_engine_axioms_before)
         axioms_after) then
    failwith "disjunctive family engine: checkpoint state invalid";;

let candle_disjunctive_family_engine_prove_next state count =
  if count <= 0 then
    failwith "disjunctive family engine: empty chunk";
  let requested = !(state.family_engine_next_index) + count in
  let target =
    if requested > state.family_engine_leaf_count then
      state.family_engine_leaf_count
    else requested in
  let rec advance () =
    if !(state.family_engine_next_index) < target then begin
      candle_disjunctive_family_engine_prove_one state
        !(state.family_engine_next_index);
      advance ()
    end in
  advance ();
  candle_disjunctive_family_engine_validate_state state;
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_FAMILY_ENGINE_PROGRESS" ^
     " family=" ^ state.family_engine_label ^
     " proved=" ^ string_of_int !(state.family_engine_next_index) ^
     "/" ^ string_of_int state.family_engine_leaf_count ^
     " total_attempts=" ^
     string_of_int !(state.family_engine_total_attempts) ^
     " total_cells=" ^
     string_of_int !(state.family_engine_total_cells) ^
     " retained_theorems=" ^
     string_of_int (length !(state.family_engine_results)));;

let candle_disjunctive_family_engine_ordered_theorems state =
  if !(state.family_engine_next_index) <>
       state.family_engine_leaf_count then
    failwith "disjunctive family engine: incomplete theorem set";
  map
    (fun result -> result.family_engine_leaf_proof.
      disjunctive_fixed_outer_theorem)
    (rev !(state.family_engine_results));;

let candle_disjunctive_family_engine_glue_root state tree =
  let rec glue tree sources =
    match tree with
    | P_result_pass (_,function_index,raw_flag) ->
        if function_index <> state.family_engine_function_index ||
           raw_flag then
          failwith "disjunctive family engine: pass selection mismatch";
        (match sources with
         | theorem::remaining -> theorem,remaining
         | [] -> failwith "disjunctive family engine: missing theorem")
    | P_result_glue (_,split_index,convex_flag,left,right) ->
        if convex_flag then
          failwith "disjunctive family engine: convex node";
        let left_theorem,after_left = glue left sources in
        let right_theorem,remaining = glue right after_left in
        let appended =
          M_verifier.m_glue_cells_list 6 (split_index + 1)
            left_theorem right_theorem in
        M_verifier.merge_m_cell_list_pass 6 appended,remaining
    | P_result_mono _ ->
        failwith "disjunctive family engine: monotonicity node"
    | P_result_ref _ ->
        failwith "disjunctive family engine: reference node" in
  let root,remaining =
    glue tree (candle_disjunctive_family_engine_ordered_theorems state) in
  if remaining <> [] then
    failwith "disjunctive family engine: trailing theorem";
  root;;

end;;
