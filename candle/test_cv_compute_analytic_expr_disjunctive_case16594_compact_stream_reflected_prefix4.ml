(* Genuine first-four-cell discriminator for a reflected compact stream. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_compact_stream_prefix4_fixture.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_compute.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16594_compact_stream_reflected_prefix4 = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_compute;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_compact_stream_prefix4_fixture;;

let _ =
  let axioms_before = axioms () in
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE" ^
         " lane=disjunctive-case16594-reflected-prefix4" ^
         " phase=" ^ event));
  let prepared =
    candle_disjunctive_case16594_prefix4_fixture_prepared in
  let cells =
    candle_disjunctive_case16594_prefix4_fixture_cells in
  let segment_items,remaining_tokens =
    candle_disjunctive_case16594_prefix4_fixture_segment_items,
    candle_disjunctive_case16594_prefix4_fixture_remaining_tokens in
  let segment =
    candle_disjunctive_case16594_prefix4_fixture_segment in
  let encoded_segment =
    candle_disjunctive_case16594_prefix4_fixture_encoded_segment in
  let raw =
    candle_disjunctive_case16594_prefix4_fixture_raw in
  let reflected_call =
    list_mk_comb
      (`candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run`,
       [`Cexp_num 6`;encoded_segment;raw.variable_raw_encoded_jobs_term;
        `Cexp_num 0`]) in
  print_endline
    ("CANDLE_CERT_PROFILE lane=disjunctive-case16594-reflected-prefix4" ^
     " scope=reflected phase=compact-compute event=begin");
  let reflected_theorem =
    Kernel.compute
      (COMPUTE_INIT_THMS,
       candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_compute_eqs)
      reflected_call in
  print_endline
    ("CANDLE_CERT_PROFILE lane=disjunctive-case16594-reflected-prefix4" ^
     " scope=reflected phase=compact-compute event=end");
  let reflected_success,reflected_payload =
    candle_q_dim_stable_program_dest_cval_pair
      "case16594 reflected prefix4 result" (rand (concl reflected_theorem)) in
  let reflected_remaining,reflected_stack =
    candle_q_dim_stable_program_dest_cval_pair
      "case16594 reflected prefix4 payload" reflected_payload in
  let reflected_root,reflected_stack_tail =
    candle_q_dim_stable_program_dest_cval_pair
      "case16594 reflected prefix4 stack" reflected_stack in
  print_endline
    ("CANDLE_CERT_PROFILE lane=disjunctive-case16594-reflected-prefix4" ^
     " scope=native-control phase=compact-step event=begin");
  let native_state =
    candle_q_dim_taylor_model_fixed_outer_variable_compact_step_six
      prepared
      (candle_q_dim_taylor_model_fixed_outer_variable_compact_initial_six
        prepared)
      raw.variable_raw_decoded_jobs_term raw.variable_raw_accept_theorem
      segment in
  print_endline
    ("CANDLE_CERT_PROFILE lane=disjunctive-case16594-reflected-prefix4" ^
     " scope=native-control phase=compact-step event=end");
  let native_root =
    match dest_list native_state.variable_compact_state_stack_term with
    | [root] -> root
    | _ -> failwith "case16594 reflected prefix4: native non-singleton stack" in
  let native_root_encoding =
    candle_q_dim_analytic_jet_boxes_encode_conv native_root in
  let axioms_after = axioms () in
  if length cells <> 4 || length segment_items <> 7 ||
     remaining_tokens = [] || hyp reflected_theorem <> [] ||
     not (aconv reflected_success `Cexp_num 1`) ||
     not (aconv reflected_remaining `Cexp_num 0`) ||
     not (aconv reflected_stack_tail `Cexp_num 0`) ||
     not (aconv reflected_root (rand (concl native_root_encoding))) ||
     hyp native_state.variable_compact_state_pass_theorem <> [] ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case16594 reflected prefix4: validation failed";
  print_endline
    "CANDLE_CV_DISJUNCTIVE_CASE16594_REFLECTED_PREFIX4_RESULT numerical_cells=4 token_items=7 active_roots=1 assumptions=0 roots_match=true";
  print_endline
    "CANDLE_CV_DISJUNCTIVE_CASE16594_REFLECTED_PREFIX4_OK DEVELOPMENT_NON_RELEASE";;

end;;
