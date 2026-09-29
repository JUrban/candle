(* ========================================================================== *)
(* Complete a proved case-10173 leaf forest to the original ineqm theorem.   *)
(*                                                                            *)
(* The reflected fixed-outer replay has already proved one theorem for every *)
(* authenticated precision leaf.  This adapter consumes those theorems in   *)
(* exact tree order, reconstructs the original certificate root, applies the *)
(* verifier's standard normalization, and transports through the two pinned  *)
(* source conversions back to the literal Flyspeck statement.                *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_leaf_grouping_fixture.ml";;
needs "candle/test_cv_compute_analytic_expr_action296_fixed_outer_grouped_policy_proof.ml";;

open Certificate;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_case10173_fixture;;
open Candle_cv_analytic_expr_case10173_reused_plan;;
open Candle_cv_action296_adaptive_forest_prove;;
open Candle_cv_action296_stable_grouped_forest_prove;;

let candle_case10173_complete_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=case10173-completion" ^
     " scope=source phase=" ^ phase ^ " event=" ^ event);;

let candle_case10173_complete_axioms_before = axioms ();;
let candle_case10173_complete_forest =
  (candle_action296_fixed_outer_grouped_result ()).
    stable_group_forest_result;;

let rec candle_case10173_complete_ordered expected = function
  | [] -> expected = 3305
  | (index,theorem) :: remaining ->
      index = expected && hyp theorem = [] &&
      candle_case10173_complete_ordered (expected + 1) remaining;;

if candle_case10173_complete_forest.forest_result_original_roots <> 3305 ||
   not
     (candle_case10173_complete_ordered 0
       candle_case10173_complete_forest.forest_result_theorems) then
  failwith "case10173 completion: forest identity mismatch";;

let rec candle_case10173_complete_glue tree sources =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 0 || raw_flag then
        failwith "case10173 completion: unexpected pass selection";
      (match sources with
       | (_,theorem) :: remaining -> theorem,remaining
       | [] -> failwith "case10173 completion: missing leaf theorem")
  | P_result_glue (_,split_index,convex_flag,left,right) ->
      if convex_flag then
        failwith "case10173 completion: unexpected convex branch";
      let left_theorem,after_left =
        candle_case10173_complete_glue left sources in
      let right_theorem,remaining =
        candle_case10173_complete_glue right after_left in
      let appended =
        M_verifier.m_glue_cells_list candle_action296_plan_dimension
          (split_index + 1) left_theorem right_theorem in
      M_verifier.merge_m_cell_list_pass
        candle_action296_plan_dimension appended,
      remaining
  | P_result_mono _ ->
      failwith "case10173 completion: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "case10173 completion: unexpected reference node";;

let candle_case10173_complete_reconstruct root_list_pass =
  let functions,domain =
    M_verifier.dest_m_cell_list_pass (concl root_list_pass) in
  let expected_domain =
    let root_domain,_,_ =
      M_taylor.dest_m_cell_domain
        (concl candle_case10173_leaf_grouping_root_domain) in
    root_domain in
  if functions <> [candle_action296_plan_prepared.function_term] ||
     not (aconv domain expected_domain) || hyp root_list_pass <> [] then
    failwith "case10173 completion: root theorem mismatch";
  let _ =
    candle_case10173_complete_marker "source-reconstruction" "begin" in
  let cell_goal =
    list_mk_comb
      (`m_cell_pass:(real^6->real)->(real^6#real^6)->bool`,
       [candle_action296_plan_prepared.function_term;domain]) in
  let cell_expansion =
    REWRITE_CONV [M_verifier.M_CELL_PASS_EQ_LIST_PASS1] cell_goal in
  let cell_pass = EQ_MP (SYM cell_expansion) root_list_pass in
  let converted =
    M_verifier_main.normalize_result true
      candle_case10173_analytic_variable_vector
      candle_case10173_analytic_standard
      candle_case10173_plan_domain_subset cell_pass in
  if hyp converted <> [] ||
     not
       (aconv (concl converted) candle_case10173_analytic_converted) then
    failwith "case10173 completion: normalized source mismatch";
  let case_theorem =
    EQ_MP (SYM candle_case10173_analytic_expansion) converted in
  let theorem =
    EQ_MP (SYM candle_case10173_analytic_reconstruction) case_theorem in
  let _ =
    candle_case10173_complete_marker "source-reconstruction" "end" in
  theorem;;

let _ = candle_case10173_complete_marker "precision-tree-glue" "begin";;
let candle_case10173_complete_root_list_pass,
    candle_case10173_complete_remaining =
  candle_case10173_complete_glue
    candle_case10173_plan_precision_tree
    candle_case10173_complete_forest.forest_result_theorems;;
let _ = candle_case10173_complete_marker "precision-tree-glue" "end";;

if candle_case10173_complete_remaining <> [] then
  failwith "case10173 completion: trailing leaf theorem";;

let candle_case10173_complete_theorem =
  candle_case10173_complete_reconstruct
    candle_case10173_complete_root_list_pass;;

let candle_case10173_complete_axioms_after = axioms ();;
if hyp candle_case10173_complete_theorem <> [] ||
   not
     (aconv (concl candle_case10173_complete_theorem)
       candle_case10173_analytic_target) ||
   length candle_case10173_complete_axioms_after <>
     length candle_case10173_complete_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_case10173_complete_axioms_before)
       candle_case10173_complete_axioms_after) then
  failwith "case10173 completion: final theorem validation failed";;

print_endline
  ("CANDLE_CV_CASE10173_COMPLETE_RESULT roots=3305 final_cells=" ^
   string_of_int
     candle_case10173_complete_forest.forest_result_final_cells ^
   " forest_digest=" ^
   candle_case10173_complete_forest.forest_result_digest ^
   " theorem_digest=" ^
   Digest.to_hex
     (Digest.string (string_of_thm candle_case10173_complete_theorem)));;
print_endline
  "CANDLE_CV_CASE10173_COMPLETE_OK DEVELOPMENT_NON_RELEASE";;
