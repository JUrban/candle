(* Complete genuine case-16594 root and source theorem from one reflected call. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_complete_full_precomputed_capture.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_complete_root_prove.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16594_complete_full_precomputed_handoff = struct

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
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_root_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_axis_plan;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_complete_full_precomputed_capture;;

let candle_disjunctive_case16594_complete_full_logical_token = function
  | Candle_disjunctive_case16594_complete_full_leaf ->
      `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf`
  | Candle_disjunctive_case16594_complete_full_glue axis ->
      mk_comb
        (`Candle_q_dim_taylor_model_fixed_outer_variable_compact_glue`,
         mk_small_numeral axis);;

let _ =
  let axioms_before = axioms () in
  let captured = candle_disjunctive_case16594_complete_full_precomputed () in
  let leaf =
    `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf` in
  let token_data,leaf_count,glue_count =
    candle_disjunctive_case16594_complete_full_traverse
      [Candle_disjunctive_case16594_complete_full_visit
        (candle_disjunctive_case16594_variable_axis_plan ())]
      [] 0 0 in
  if leaf_count <> 875 || glue_count <> 874 || length token_data <> 1749 then
    failwith "case16594 complete full handoff: token plan shape mismatch";
  let token_items =
    map candle_disjunctive_case16594_complete_full_logical_token
      token_data in
  let tokens = mk_list (token_items,type_of leaf) in
  candle_q_dim_analytic_jet_profile_event
    "complete-full-precomputed-theorem-handoff-begin";
  let root =
    candle_q_dim_taylor_model_fixed_outer_variable_complete_handoff_computed_root_six
      captured.complete_full_prepared tokens
      captured.complete_full_encoded_tokens captured.complete_full_encoded_jobs
      captured.complete_full_compute_theorem in
  candle_q_dim_analytic_jet_profile_event
    "complete-full-precomputed-theorem-handoff-end";
  let root_lower,root_upper =
    candle_disjunctive_fixed_outer_domain_bounds
      candle_disjunctive_case16594_root_domain in
  let expected_root_boxes =
    candle_poly_fixture_q_boxes root_lower root_upper in
  if length token_items <> 1749 ||
     not (aconv root.variable_complete_root_boxes_term expected_root_boxes)
  then failwith "case16594 complete full handoff: root box drift";
  candle_q_dim_analytic_jet_profile_event
    "complete-full-precomputed-source-completion-begin";
  let root_list_pass =
    candle_reflected_nl_source_pass_with
      candle_disjunctive_case16594_engine_state.family_engine_function_term
      (fun actual_lower actual_upper ->
        if not
            (candle_disjunctive_fixed_outer_aconv_lists
               actual_lower root_lower &&
             candle_disjunctive_fixed_outer_aconv_lists
               actual_upper root_upper)
        then failwith "case16594 complete full handoff: root handoff drift";
        root.variable_complete_root_source_theorem)
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
  candle_q_dim_analytic_jet_profile_event
    "complete-full-precomputed-source-completion-end";
  let axioms_after = axioms () in
  let digest = Digest.to_hex (Digest.string (string_of_thm theorem)) in
  if hyp root.variable_complete_root_cell_theorem <> [] ||
     hyp root.variable_complete_root_source_theorem <> [] ||
     hyp theorem <> [] ||
     not (aconv (concl theorem) candle_disjunctive_case16594_target) ||
     digest <> "8bb2c1bf3d1c1944d497c0da68b88207" ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case16594 complete full handoff: final validation failed";
  print_endline
    ("CANDLE_CV_CASE16594_COMPLETE_FULL_HANDOFF_OK DEVELOPMENT_NON_RELEASE" ^
     " authenticated_leaves=860 numerical_cells=875 token_items=1749" ^
     " active_roots=1 remaining_jobs=0 assumptions=0 axiom_growth=0" ^
     " theorem_digest=" ^ digest);;

end;;
