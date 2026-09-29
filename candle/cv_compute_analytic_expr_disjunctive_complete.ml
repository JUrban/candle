(* ========================================================================== *)
(* Complete the reflected 788-leaf disjunctive proof to its source theorem.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The checkpointed family prover has already   *)
(* produced one closed kernel theorem for every authenticated precision      *)
(* leaf.  This adapter consumes those theorems in exact tree order, rebuilds *)
(* the verifier root, and transports the result through the pinned source    *)
(* conversions to the literal Flyspeck statement.                            *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_disjunctive_family_prove.ml";;

module Candle_cv_analytic_expr_disjunctive_complete = struct

open Certificate;;
open Candle_cv_analytic_expr_disjunctive_fixture;;
open Candle_cv_analytic_expr_disjunctive_plan;;
open Candle_cv_analytic_expr_disjunctive_leaf_grouping_fixture;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;
open Candle_cv_analytic_expr_disjunctive_family_prove;;

let candle_disjunctive_complete_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=disjunctive-completion" ^
     " scope=source phase=" ^ phase ^ " event=" ^ event);;

let candle_disjunctive_complete_axioms_before = axioms ();;

let candle_disjunctive_complete_results =
  rev !candle_disjunctive_family_results;;

let rec candle_disjunctive_complete_ordered expected = function
  | [] -> expected = 788
  | result :: remaining ->
      result.disjunctive_family_leaf_index = expected &&
      hyp
        result.disjunctive_family_leaf_proof.
          disjunctive_fixed_outer_theorem = [] &&
      candle_disjunctive_complete_ordered (expected + 1) remaining;;

if !candle_disjunctive_family_next_index <> 788 ||
   length candle_disjunctive_complete_results <> 788 ||
   not (candle_disjunctive_complete_ordered
          0 candle_disjunctive_complete_results) then
  failwith "disjunctive completion: family state mismatch";;

let candle_disjunctive_complete_theorems =
  map
    (fun result ->
      result.disjunctive_family_leaf_proof.
        disjunctive_fixed_outer_theorem)
    candle_disjunctive_complete_results;;

let rec candle_disjunctive_complete_glue tree sources =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 1 || raw_flag then
        failwith "disjunctive completion: unexpected pass selection";
      (match sources with
       | theorem :: remaining -> theorem,remaining
       | [] -> failwith "disjunctive completion: missing leaf theorem")
  | P_result_glue (_,split_index,convex_flag,left,right) ->
      if convex_flag then
        failwith "disjunctive completion: unexpected convex branch";
      let left_theorem,after_left =
        candle_disjunctive_complete_glue left sources in
      let right_theorem,remaining =
        candle_disjunctive_complete_glue right after_left in
      let appended =
        M_verifier.m_glue_cells_list 6 (split_index + 1)
          left_theorem right_theorem in
      M_verifier.merge_m_cell_list_pass 6 appended,remaining
  | P_result_mono _ ->
      failwith "disjunctive completion: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "disjunctive completion: unexpected reference node";;

let _ = candle_disjunctive_complete_marker "precision-tree-glue" "begin";;
let candle_disjunctive_complete_root_list_pass,
    candle_disjunctive_complete_remaining =
  candle_disjunctive_complete_glue
    candle_disjunctive_plan_precision_tree
    candle_disjunctive_complete_theorems;;
let _ = candle_disjunctive_complete_marker "precision-tree-glue" "end";;

if candle_disjunctive_complete_remaining <> [] then
  failwith "disjunctive completion: trailing leaf theorem";;

let candle_disjunctive_complete_functions,
    candle_disjunctive_complete_domain =
  M_verifier.dest_m_cell_list_pass
    (concl candle_disjunctive_complete_root_list_pass);;

let candle_disjunctive_complete_expected_domain =
  let domain,_,_ =
    M_taylor.dest_m_cell_domain
      (concl candle_disjunctive_leaf_grouping_root_domain) in
  domain;;

if candle_disjunctive_complete_functions <>
     [candle_disjunctive_family_function_term] ||
   not
     (aconv candle_disjunctive_complete_domain
       candle_disjunctive_complete_expected_domain) ||
   hyp candle_disjunctive_complete_root_list_pass <> [] then
  failwith "disjunctive completion: root theorem mismatch";;

let _ = candle_disjunctive_complete_marker "source-reconstruction" "begin";;
let candle_disjunctive_complete_expanded_general =
  M_verifier_main.normalize_disj_result true
    candle_disjunctive_analytic_functions
    candle_disjunctive_analytic_variable_vector
    candle_disjunctive_analytic_standard
    candle_disjunctive_plan_domain_subset
    candle_disjunctive_complete_root_list_pass;;

let candle_disjunctive_complete_expanded =
  let theorem = SPEC_ALL candle_disjunctive_complete_expanded_general in
  let bridge =
    TAUT
      (mk_imp
        (concl theorem,candle_disjunctive_analytic_converted)) in
  MP bridge theorem;;

if hyp candle_disjunctive_complete_expanded <> [] ||
   not
     (aconv (concl candle_disjunctive_complete_expanded)
       candle_disjunctive_analytic_converted) then
  failwith "disjunctive completion: normalized source mismatch";;

let candle_disjunctive_complete_case_theorem =
  REWRITE_RULE[GSYM candle_disjunctive_analytic_expansion]
    candle_disjunctive_complete_expanded;;

let candle_disjunctive_complete_theorem =
  (SPEC_ALL o
   REWRITE_RULE[GSYM candle_disjunctive_analytic_reconstruction])
    candle_disjunctive_complete_case_theorem;;
let _ = candle_disjunctive_complete_marker "source-reconstruction" "end";;

let candle_disjunctive_complete_axioms_after = axioms ();;
if hyp candle_disjunctive_complete_theorem <> [] ||
   not
     (aconv (concl candle_disjunctive_complete_theorem)
       candle_disjunctive_analytic_target) ||
   length candle_disjunctive_complete_axioms_after <>
     length candle_disjunctive_complete_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_disjunctive_complete_axioms_before)
       candle_disjunctive_complete_axioms_after) then
  failwith "disjunctive completion: final theorem validation failed";;

print_endline
  ("CANDLE_CV_DISJUNCTIVE_COMPLETE_RESULT leaves=788" ^
   " total_attempts=" ^
   string_of_int !candle_disjunctive_family_total_attempts ^
   " total_cells=" ^
   string_of_int !candle_disjunctive_family_total_cells ^
   " theorem_digest=" ^
   Digest.to_hex
     (Digest.string (string_of_thm candle_disjunctive_complete_theorem)));;
print_endline
  "CANDLE_CV_DISJUNCTIVE_COMPLETE_OK DEVELOPMENT_NON_RELEASE";;

end;;
