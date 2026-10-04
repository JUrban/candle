(* Complete genuine case-10173 theorem from one proved fixed-nonlinear verdict. *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_fixed_nonlinear_complete_capture.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_root_prove.ml";;

module Test_cv_compute_analytic_expr_case10173_fixed_nonlinear_complete_handoff = struct

open M_verifier;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_case10173_fixture;;
open Candle_cv_analytic_expr_case10173_reused_plan;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_root_prove;;
open Benchmark_cv_compute_analytic_expr_case10173_variable_raw_plan;;
open Benchmark_cv_compute_analytic_expr_case10173_complete_topology;;
open Benchmark_cv_compute_analytic_expr_case10173_complete_capture;;
open Benchmark_cv_compute_analytic_expr_case10173_fixed_nonlinear_complete_capture;;

let candle_case10173_fixed_nonlinear_complete_source_theorem_state :
    thm option ref = ref None;;

Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
  (fun event ->
    print_endline
      ("CANDLE_CERT_PROFILE lane=case10173-fixed-nonlinear-complete-handoff" ^
       " phase=" ^ event));;

let candle_case10173_fixed_nonlinear_complete_logical_token = function
  | Candle_case10173_complete_leaf ->
      `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf`
  | Candle_case10173_complete_glue axis ->
      mk_comb
        (`Candle_q_dim_taylor_model_fixed_outer_variable_compact_glue`,
         mk_small_numeral axis);;

let rec candle_case10173_fixed_nonlinear_complete_aconv_lists left right =
  match left,right with
  | [],[] -> true
  | left_head :: left_tail,right_head :: right_tail ->
      aconv left_head right_head &&
      candle_case10173_fixed_nonlinear_complete_aconv_lists
        left_tail right_tail
  | _ -> false;;

let _ =
  let axioms_before = axioms () in
  let captured = candle_case10173_complete_capture () in
  let prepared = captured.case10173_complete_prepared in
  let leaf =
    `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf` in
  let token_items =
    map candle_case10173_fixed_nonlinear_complete_logical_token
      (candle_case10173_complete_token_data ()) in
  let tokens = mk_list (token_items,type_of leaf) in
  candle_q_dim_analytic_jet_profile_event
    "case10173-fixed-nonlinear-complete-theorem-handoff-begin";
  let root =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_complete_handoff_computed_root_six
      prepared tokens captured.case10173_complete_encoded_tokens
      captured.case10173_complete_encoded_jobs
      (candle_case10173_fixed_nonlinear_complete_compute ()) in
  candle_q_dim_analytic_jet_profile_event
    "case10173-fixed-nonlinear-complete-theorem-handoff-end";
  let root_lower,root_upper =
    candle_action296_leaf_grouping_domain_bounds
      candle_case10173_leaf_grouping_root_domain in
  let expected_root_boxes =
    candle_poly_fixture_q_boxes root_lower root_upper in
  if length token_items <> 8345 ||
     not
       (aconv
         root.fixed_nonlinear_variable_complete_root_boxes_term
         expected_root_boxes)
  then failwith "case10173 fixed nonlinear complete: root box drift";
  candle_q_dim_analytic_jet_profile_event
    "case10173-fixed-nonlinear-complete-source-completion-begin";
  let root_list_pass =
    candle_reflected_nl_source_pass_with
      prepared.function_term
      (fun actual_lower actual_upper ->
        if not
            (candle_case10173_fixed_nonlinear_complete_aconv_lists
               actual_lower root_lower &&
             candle_case10173_fixed_nonlinear_complete_aconv_lists
               actual_upper root_upper)
        then failwith "case10173 fixed nonlinear complete: source box drift";
        root.fixed_nonlinear_variable_complete_root_source_theorem)
      candle_case10173_leaf_grouping_root_domain in
  let functions,domain =
    M_verifier.dest_m_cell_list_pass (concl root_list_pass) in
  let expected_domain =
    let root_domain,_,_ =
      M_taylor.dest_m_cell_domain
        (concl candle_case10173_leaf_grouping_root_domain) in
    root_domain in
  if functions <> [prepared.function_term] ||
     not (aconv domain expected_domain) || hyp root_list_pass <> [] then
    failwith "case10173 fixed nonlinear complete: root theorem mismatch";
  let cell_goal =
    list_mk_comb
      (`m_cell_pass:(real^6->real)->(real^6#real^6)->bool`,
       [prepared.function_term;domain]) in
  let cell_expansion =
    REWRITE_CONV [M_verifier.M_CELL_PASS_EQ_LIST_PASS1] cell_goal in
  let cell_pass = EQ_MP (SYM cell_expansion) root_list_pass in
  let expanded_general =
    M_verifier_main.normalize_result true
      candle_case10173_analytic_variable_vector
      candle_case10173_analytic_standard
      candle_case10173_plan_domain_subset cell_pass in
  let converted =
    let specialized = SPEC_ALL expanded_general in
    let bridge =
      TAUT
        (mk_imp
          (concl specialized,candle_case10173_analytic_converted)) in
    MP bridge specialized in
  if hyp converted <> [] ||
     concl converted <> candle_case10173_analytic_converted then
    failwith
      "case10173 fixed nonlinear complete: normalized source bridge mismatch";
  let case_theorem =
    REWRITE_RULE[GSYM candle_case10173_analytic_expansion] converted in
  let theorem =
    (SPEC_ALL o
     REWRITE_RULE[GSYM candle_case10173_analytic_reconstruction])
      case_theorem in
  candle_q_dim_analytic_jet_profile_event
    "case10173-fixed-nonlinear-complete-source-completion-end";
  let axioms_after = axioms () in
  let digest = Digest.to_hex (Digest.string (string_of_thm theorem)) in
  if hyp root.fixed_nonlinear_variable_complete_root_cell_theorem <> [] ||
     hyp root.fixed_nonlinear_variable_complete_root_source_theorem <> [] ||
     hyp theorem <> [] ||
     not (aconv (concl theorem) candle_case10173_analytic_target) ||
     digest <> "48c97d39af116042909b7896d0d83123" ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case10173 fixed nonlinear complete: final validation failed";
  candle_case10173_fixed_nonlinear_complete_source_theorem_state := Some theorem;
  print_endline
    ("CANDLE_CV_CASE10173_FIXED_NONLINEAR_COMPLETE_HANDOFF_OK" ^
     " DEVELOPMENT_NON_RELEASE roots=3305 numerical_cells=4173" ^
     " token_items=8345 active_roots=1 remaining_jobs=0" ^
     " assumptions=0 axiom_growth=0 theorem_digest=" ^ digest);;

let candle_case10173_fixed_nonlinear_complete_source_theorem () =
  match !candle_case10173_fixed_nonlinear_complete_source_theorem_state with
  | Some theorem -> theorem
  | None ->
      failwith "case10173 fixed nonlinear complete: source theorem unavailable";;

end;;
