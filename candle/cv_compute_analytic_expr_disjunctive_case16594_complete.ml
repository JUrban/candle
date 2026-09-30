(* ========================================================================== *)
(* Complete the reflected 860-leaf case16594 proof to its source theorem.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The checkpointed family engine has already   *)
(* produced one closed kernel theorem for every authenticated precision      *)
(* leaf.  This adapter rejoins the exact precision tree and transports the   *)
(* verifier result through the pinned source conversions.                    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_disjunctive_case16594_family_prove.ml";;

module Candle_cv_analytic_expr_disjunctive_case16594_complete = struct

open Certificate;;
open Candle_cv_analytic_expr_disjunctive_case16594_fixture;;
open Candle_cv_analytic_expr_disjunctive_case16594_plan;;
open Candle_cv_analytic_expr_disjunctive_case16594_leaf_grouping;;
open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;

let candle_disjunctive_case16594_complete_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=disjunctive-case16594-completion" ^
     " scope=source phase=" ^ phase ^ " event=" ^ event);;

let candle_disjunctive_case16594_complete_axioms_before = axioms ();;

let _ =
  candle_disjunctive_case16594_complete_marker
    "precision-tree-glue" "begin";;
let candle_disjunctive_case16594_complete_root_list_pass =
  candle_disjunctive_family_engine_glue_root
    candle_disjunctive_case16594_engine_state
    candle_disjunctive_case16594_plan_precision_tree;;
let _ =
  candle_disjunctive_case16594_complete_marker
    "precision-tree-glue" "end";;

let candle_disjunctive_case16594_complete_functions,
    candle_disjunctive_case16594_complete_domain =
  M_verifier.dest_m_cell_list_pass
    (concl candle_disjunctive_case16594_complete_root_list_pass);;

let candle_disjunctive_case16594_complete_expected_domain =
  let domain,_,_ =
    M_taylor.dest_m_cell_domain
      (concl candle_disjunctive_case16594_root_domain) in
  domain;;

if candle_disjunctive_case16594_complete_functions <>
     [candle_disjunctive_case16594_engine_state.family_engine_function_term] ||
   not
     (aconv candle_disjunctive_case16594_complete_domain
       candle_disjunctive_case16594_complete_expected_domain) ||
   hyp candle_disjunctive_case16594_complete_root_list_pass <> [] then
  failwith "case16594 completion: root theorem mismatch";;

let _ =
  candle_disjunctive_case16594_complete_marker
    "source-reconstruction" "begin";;
let candle_disjunctive_case16594_complete_expanded_general =
  M_verifier_main.normalize_disj_result true
    candle_disjunctive_case16594_functions
    candle_disjunctive_case16594_variable_vector
    candle_disjunctive_case16594_standard
    candle_disjunctive_case16594_plan_domain_subset
    candle_disjunctive_case16594_complete_root_list_pass;;

let candle_disjunctive_case16594_complete_expanded =
  let theorem =
    SPEC_ALL candle_disjunctive_case16594_complete_expanded_general in
  let bridge =
    TAUT
      (mk_imp
        (concl theorem,candle_disjunctive_case16594_converted)) in
  MP bridge theorem;;

if hyp candle_disjunctive_case16594_complete_expanded <> [] ||
   not
     (aconv (concl candle_disjunctive_case16594_complete_expanded)
       candle_disjunctive_case16594_converted) then
  failwith "case16594 completion: normalized source mismatch";;

let candle_disjunctive_case16594_complete_case_theorem =
  REWRITE_RULE[GSYM candle_disjunctive_case16594_expansion]
    candle_disjunctive_case16594_complete_expanded;;

let candle_disjunctive_case16594_complete_theorem =
  (SPEC_ALL o
   REWRITE_RULE[GSYM candle_disjunctive_case16594_reconstruction])
    candle_disjunctive_case16594_complete_case_theorem;;
let _ =
  candle_disjunctive_case16594_complete_marker
    "source-reconstruction" "end";;

let candle_disjunctive_case16594_complete_axioms_after = axioms ();;
if hyp candle_disjunctive_case16594_complete_theorem <> [] ||
   not
     (aconv (concl candle_disjunctive_case16594_complete_theorem)
       candle_disjunctive_case16594_target) ||
   length candle_disjunctive_case16594_complete_axioms_after <>
     length candle_disjunctive_case16594_complete_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem
           candle_disjunctive_case16594_complete_axioms_before)
       candle_disjunctive_case16594_complete_axioms_after) then
  failwith "case16594 completion: final theorem validation failed";;

print_endline
  ("CANDLE_CV_DISJUNCTIVE_CASE16594_COMPLETE_RESULT leaves=860" ^
   " total_attempts=" ^
   string_of_int
     !(candle_disjunctive_case16594_engine_state.
       family_engine_total_attempts) ^
   " total_cells=" ^
   string_of_int
     !(candle_disjunctive_case16594_engine_state.
       family_engine_total_cells) ^
   " theorem_digest=" ^
   Digest.to_hex
     (Digest.string
       (string_of_thm
         candle_disjunctive_case16594_complete_theorem)));;
print_endline
  "CANDLE_CV_DISJUNCTIVE_CASE16594_COMPLETE_OK DEVELOPMENT_NON_RELEASE";;

end;;
