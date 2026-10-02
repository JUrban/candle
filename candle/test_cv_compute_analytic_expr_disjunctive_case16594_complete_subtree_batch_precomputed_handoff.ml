(* Late theorem handoff for four genuine complete case-16594 subtrees.
   DEVELOPMENT / NON-RELEASE only. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_complete_subtree_batch_precomputed_capture.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_complete_prove.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16594_complete_subtree_batch_precomputed_handoff = struct

open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_complete_subtree_batch_precomputed_capture;;

let candle_disjunctive_case16594_complete_subtree_batch_logical_token = function
  | Candle_disjunctive_case16594_complete_subtree_batch_leaf ->
      `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf`
  | Candle_disjunctive_case16594_complete_subtree_batch_glue axis ->
      mk_comb
        (`Candle_q_dim_taylor_model_fixed_outer_variable_compact_glue`,
         mk_small_numeral axis);;

let rec candle_disjunctive_case16594_complete_subtree_batch_handoff_stack_length
    encoded =
  if aconv encoded `Cexp_num 0` then 0
  else
    let _,tail =
      candle_q_dim_stable_program_dest_cval_pair
        "case16594 complete subtree batch handoff stack" encoded in
    1 +
    candle_disjunctive_case16594_complete_subtree_batch_handoff_stack_length
      tail;;

let candle_disjunctive_case16594_complete_subtree_batch_handoff_profile
    start phase =
  print_endline
    ("CANDLE_CERT_PROFILE" ^
     " lane=disjunctive-case16594-complete-subtree-batch" ^
     " phase=segment-" ^ string_of_int start ^ "-" ^ phase);;

let rec candle_disjunctive_case16594_complete_subtree_batch_handoff
    prepared = function
  | [] -> 0
  | captured :: remaining ->
      let token_items =
        map candle_disjunctive_case16594_complete_subtree_batch_logical_token
          captured.complete_subtree_batch_token_data in
      let leaf =
        `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf` in
      let tokens = mk_list (token_items,type_of leaf) in
      candle_disjunctive_case16594_complete_subtree_batch_handoff_profile
        captured.complete_subtree_batch_start "theorem-handoff-begin";
      let result =
        candle_q_dim_taylor_model_fixed_outer_variable_complete_handoff_computed_stack_six
          prepared tokens captured.complete_subtree_batch_encoded_tokens
          captured.complete_subtree_batch_encoded_jobs
          captured.complete_subtree_batch_compute_theorem in
      candle_disjunctive_case16594_complete_subtree_batch_handoff_profile
        captured.complete_subtree_batch_start "theorem-handoff-end";
      let active_roots =
        candle_disjunctive_case16594_complete_subtree_batch_handoff_stack_length
          result.variable_complete_encoded_stack_term in
      if length token_items <> 2 * captured.complete_subtree_batch_cells - 1 ||
         active_roots <> 1 ||
         hyp result.variable_complete_compute_theorem <> [] ||
         hyp result.variable_complete_stack_theorem <> [] then
        failwith "case16594 complete subtree batch handoff: validation failed";
      print_endline
        ("CANDLE_CV_CASE16594_COMPLETE_SUBTREE_BATCH_HANDOFF_SEGMENT_RESULT" ^
         " start=" ^ string_of_int captured.complete_subtree_batch_start ^
         " numerical_cells=" ^
           string_of_int captured.complete_subtree_batch_cells ^
         " token_items=" ^ string_of_int (length token_items) ^
         " active_roots=1 assumptions=0");
      1 +
      candle_disjunctive_case16594_complete_subtree_batch_handoff
        prepared remaining;;

let _ =
  let axioms_before = axioms () in
  let captured =
    candle_disjunctive_case16594_complete_subtree_batch_precomputed () in
  let count =
    candle_disjunctive_case16594_complete_subtree_batch_handoff
      captured.complete_subtree_batch_prepared
      captured.complete_subtree_batch_segments in
  let axioms_after = axioms () in
  if count <> 4 || length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case16594 complete subtree batch handoff: axiom validation";
  print_endline
    "CANDLE_CV_CASE16594_COMPLETE_SUBTREE_BATCH_HANDOFF_OK DEVELOPMENT_NON_RELEASE segments=4 numerical_cells=64 active_roots=4 assumptions=0 axiom_growth=0";;

end;;
