(* ========================================================================== *)
(* Complete member 16594 through bounded raw batches and a box-free topology. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Numerical batches are checked independently,  *)
(* combined only by the proved jobs-accept APPEND law, and discharged by the  *)
(* universal compact-stack theorem.  The topology stream carries split axes  *)
(* but no duplicated parent boxes or analytic proof objects.                  *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_compact_token_plan.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_combine_prove.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_prove.ml";;

module Candle_cv_analytic_expr_disjunctive_case16594_compact_stack_complete_prove = struct

open Certificate;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;
open Candle_cv_analytic_expr_disjunctive_case16594_fixture;;
open Candle_cv_analytic_expr_disjunctive_case16594_plan;;
open Candle_cv_analytic_expr_disjunctive_case16594_leaf_grouping;;
open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_combine_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_compact_token_plan;;

let rec candle_disjunctive_case16594_compact_complete_split_chunks size items =
  if size <= 0 then invalid_arg "case16594 compact stack chunk size";
  let rec take remaining prefix suffix =
    if remaining = 0 then rev prefix,suffix
    else
      match suffix with
      | [] -> rev prefix,[]
      | head :: tail -> take (remaining - 1) (head :: prefix) tail in
  match items with
  | [] -> []
  | _ ->
      let prefix,suffix = take size [] items in
      prefix ::
      candle_disjunctive_case16594_compact_complete_split_chunks size suffix;;

let rec candle_disjunctive_case16594_compact_complete_prove_chunks
    prepared total index = function
  | [] -> []
  | cells :: remaining ->
      let count = length cells in
      print_endline
        ("CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_COMPLETE_CHUNK" ^
         " event=begin index=" ^ string_of_int index ^
         " total=" ^ string_of_int total ^
         " cells=" ^ string_of_int count);
      let acceptance =
        candle_q_dim_taylor_model_fixed_outer_variable_raw_acceptance_of_result
          (candle_q_dim_taylor_model_fixed_outer_variable_raw_prove_six
            prepared cells) in
      print_endline
        ("CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_COMPLETE_CHUNK" ^
         " event=end index=" ^ string_of_int index ^
         " total=" ^ string_of_int total ^
         " cells=" ^ string_of_int count);
      acceptance ::
      candle_disjunctive_case16594_compact_complete_prove_chunks
        prepared total (index + 1) remaining;;

let candle_disjunctive_case16594_compact_stack_complete_prove () =
  let axioms_before = axioms () in
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE" ^
         " lane=disjunctive-case16594-compact-stack-complete" ^
         " phase=" ^ event));
  let chunks =
    candle_disjunctive_case16594_compact_complete_split_chunks 32
      candle_disjunctive_case16594_variable_raw_plan_cells in
  let chunk_count = length chunks in
  if chunk_count <> 28 then
    failwith "case16594 compact stack complete: chunk count mismatch";
  let acceptances =
    candle_disjunctive_case16594_compact_complete_prove_chunks
      candle_disjunctive_case16594_engine_state.family_engine_prepared
      chunk_count 0 chunks in
  let combined =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_acceptance_collapse
      acceptances in
  if combined.variable_raw_acceptance_compute_count <> chunk_count then
    failwith "case16594 compact stack complete: compute count mismatch";
  let compact_result =
    candle_q_dim_taylor_model_fixed_outer_variable_compact_acceptance_six
      combined.variable_raw_acceptance_prepared
      combined.variable_raw_acceptance_jobs_term
      combined.variable_raw_acceptance_theorem
      (candle_disjunctive_case16594_compact_token_plan ()) in
  let source = compact_result.variable_compact_core_source_theorem in
  let root_lower,root_upper =
    candle_disjunctive_fixed_outer_domain_bounds
      candle_disjunctive_case16594_root_domain in
  let expected_root_boxes = candle_poly_fixture_q_boxes root_lower root_upper in
  if not
      (aconv compact_result.variable_compact_core_root_boxes_term
        expected_root_boxes) then
    failwith "case16594 compact stack complete: root box drift";
  let root_list_pass =
    candle_reflected_nl_source_pass_with
      candle_disjunctive_case16594_engine_state.family_engine_function_term
      (fun actual_lower actual_upper ->
        if not
            (candle_disjunctive_fixed_outer_aconv_lists actual_lower root_lower &&
             candle_disjunctive_fixed_outer_aconv_lists actual_upper root_upper)
        then failwith "case16594 compact stack complete: root handoff drift";
        source)
      candle_disjunctive_case16594_root_domain in
  let expanded_general =
    M_verifier_main.normalize_disj_result true
      candle_disjunctive_case16594_functions
      candle_disjunctive_case16594_variable_vector
      candle_disjunctive_case16594_standard
      candle_disjunctive_case16594_plan_domain_subset
      root_list_pass in
  let expanded =
    let theorem = SPEC_ALL expanded_general in
    let bridge =
      TAUT (mk_imp (concl theorem,candle_disjunctive_case16594_converted)) in
    MP bridge theorem in
  let case_theorem =
    REWRITE_RULE[GSYM candle_disjunctive_case16594_expansion] expanded in
  let theorem =
    (SPEC_ALL o REWRITE_RULE[GSYM candle_disjunctive_case16594_reconstruction])
      case_theorem in
  let axioms_after = axioms () in
  let digest = Digest.to_hex (Digest.string (string_of_thm theorem)) in
  if hyp theorem <> [] ||
     not (aconv (concl theorem) candle_disjunctive_case16594_target) ||
     digest <> "8bb2c1bf3d1c1944d497c0da68b88207" ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case16594 compact stack complete: final validation failed";
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_STACK_COMPLETE_RESULT" ^
     " authenticated_leaves=860 numerical_cells=875 glue_nodes=874" ^
     " numerical_computes=" ^ string_of_int chunk_count ^
     " topology_reductions=1 root_handoffs=1 assumptions=0" ^
     " theorem_digest=" ^ digest);
  print_endline
    "CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_STACK_COMPLETE_OK DEVELOPMENT_NON_RELEASE";
  theorem;;

end;;
