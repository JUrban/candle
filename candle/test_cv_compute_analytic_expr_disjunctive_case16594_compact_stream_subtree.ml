(* Genuine two-cell case-16594 check of incremental compact-stack state. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_token_subtree.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_prove.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16594_compact_stream_subtree = struct

open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_token_subtree;;

let candle_disjunctive_case16594_compact_stream_subtree_leaf =
  `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf`;;

let candle_disjunctive_case16594_compact_stream_subtree_glue axis =
  mk_comb
    (`Candle_q_dim_taylor_model_fixed_outer_variable_compact_glue`,
     mk_small_numeral axis);;

let _ =
  let axioms_before = axioms () in
  let raw = candle_disjunctive_case16594_variable_token_raw in
  let tokens =
    mk_list
      ([candle_disjunctive_case16594_compact_stream_subtree_leaf;
        candle_disjunctive_case16594_compact_stream_subtree_leaf;
        candle_disjunctive_case16594_compact_stream_subtree_glue 1],
       type_of candle_disjunctive_case16594_compact_stream_subtree_leaf) in
  let initial =
    candle_q_dim_taylor_model_fixed_outer_variable_compact_initial_six
      raw.variable_raw_prepared_source in
  let final_state =
    candle_q_dim_taylor_model_fixed_outer_variable_compact_step_six
      raw.variable_raw_prepared_source initial
      raw.variable_raw_decoded_jobs_term raw.variable_raw_accept_theorem
      tokens in
  let root_boxes,theorem =
    candle_q_dim_taylor_model_fixed_outer_variable_compact_finish_six
      raw.variable_raw_prepared_source final_state in
  let expected = candle_disjunctive_case16594_variable_token_theorem in
  let digest = Digest.to_hex (Digest.string (string_of_thm theorem)) in
  let axioms_after = axioms () in
  if hyp theorem <> [] || not (aconv (concl theorem) (concl expected)) ||
     not
       (aconv root_boxes
         candle_disjunctive_case16594_variable_token_root_boxes) ||
     digest <> "d88ef874dd7e0fdf114cb999e0bfcd55" ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case16594 compact stream subtree: validation failed";
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_STREAM_SUBTREE_RESULT" ^
     " numerical_cells=2 token_segments=1 final_stack_roots=1" ^
     " assumptions=0 theorem_digest=" ^ digest);
  print_endline
    "CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_STREAM_SUBTREE_OK DEVELOPMENT_NON_RELEASE";;

end;;
