(* Genuine first-four-cell discriminator with one compact token per proof. *)

needs "candle/cv_compute_analytic_expr_disjunctive_case16594_compact_stack_complete_prove.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16594_compact_stream_tokenwise_prefix4 = struct

open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_tree_compact;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_compact_token_plan;;
open Candle_cv_analytic_expr_disjunctive_case16594_compact_stack_complete_prove;;

type candle_disjunctive_case16594_tokenwise_state = {
  tokenwise_jobs_term : term;
  tokenwise_jobs_accept_theorem : thm;
  tokenwise_stack_term : term;
  tokenwise_stack_pass_theorem : thm;
};;

let rec candle_disjunctive_case16594_tokenwise_prefix4_take count = function
  | _ when count = 0 -> []
  | [] -> failwith "case16594 tokenwise prefix4: short cell plan"
  | head :: tail ->
      head ::
      candle_disjunctive_case16594_tokenwise_prefix4_take (count - 1) tail;;

let candle_disjunctive_case16594_tokenwise_step prepared index state token =
  let token_list = mk_list ([token],type_of token) in
  let run_call =
    mk_icomb
      (mk_icomb
        (mk_icomb
          (mk_icomb
            (`candle_q_dim_taylor_model_fixed_outer_variable_compact_run`,
             `6`),
           token_list),
         state.tokenwise_jobs_term),
       state.tokenwise_stack_term) in
  print_endline
    ("CANDLE_CERT_PROFILE lane=disjunctive-case16594-tokenwise-prefix4" ^
     " scope=token-" ^ string_of_int index ^
     " phase=reduction event=begin");
  let run_theorem =
    REWRITE_CONV
      (candle_q_dim_taylor_model_fixed_outer_variable_compact_num_rewrites_six @
       [candle_q_dim_taylor_model_fixed_outer_variable_compact_run_def;
        candle_q_dim_taylor_model_fixed_outer_variable_compact_join_def;
        candle_q_boxes_split_exact_from_def;
        candle_cv_fso_variable_jobs_decode_def;
        candle_cv_fso_variable_job_decode_def;
        candle_cv_q_interval_list_decode_def;
        candle_cv_q_interval_decode_def;candle_cv_q_decode_def;
        candle_cv_lc_z_decode_def;candle_cv_lc_num_decode_def;
        cexp_fst_def;cexp_snd_def;FST;SND;APPEND;LENGTH;
        LET_DEF;LET_END_DEF])
      run_call in
  print_endline
    ("CANDLE_CERT_PROFILE lane=disjunctive-case16594-tokenwise-prefix4" ^
     " scope=token-" ^ string_of_int index ^
     " phase=reduction event=end");
  print_endline
    ("CANDLE_CERT_PROFILE lane=disjunctive-case16594-tokenwise-prefix4" ^
     " scope=token-" ^ string_of_int index ^
     " phase=proof-composition event=begin");
  let success,payload = dest_pair (rand (concl run_theorem)) in
  let remaining_jobs,final_stack = dest_pair payload in
  if not (aconv success `T`) then
    failwith "case16594 tokenwise prefix4: token rejected";
  let soundness =
    REWRITE_RULE
      [candle_q_dim_analytic_jet_dim_six]
      (ISPECL
        [token_list;prepared.expression_term;`ARB:real^6`;
         state.tokenwise_jobs_term;state.tokenwise_stack_term;
         remaining_jobs;final_stack]
        candle_q_dim_taylor_model_fixed_outer_variable_compact_run_sound) in
  let premise =
    CONJ prepared.valid_theorem
      (CONJ state.tokenwise_jobs_accept_theorem
        (CONJ state.tokenwise_stack_pass_theorem run_theorem)) in
  let conclusion = MATCH_MP soundness premise in
  print_endline
    ("CANDLE_CERT_PROFILE lane=disjunctive-case16594-tokenwise-prefix4" ^
     " scope=token-" ^ string_of_int index ^
     " phase=proof-composition event=end");
  {tokenwise_jobs_term = remaining_jobs;
   tokenwise_jobs_accept_theorem = CONJUNCT1 conclusion;
   tokenwise_stack_term = final_stack;
   tokenwise_stack_pass_theorem = CONJUNCT2 conclusion};;

let _ =
  let axioms_before = axioms () in
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE" ^
         " lane=disjunctive-case16594-tokenwise-prefix4" ^
         " phase=" ^ event));
  let prepared =
    candle_disjunctive_case16594_engine_state.family_engine_prepared in
  let cells =
    candle_disjunctive_case16594_tokenwise_prefix4_take 4
      candle_disjunctive_case16594_variable_raw_plan_cells in
  let segment_items,remaining_tokens =
    candle_disjunctive_case16594_compact_complete_take_token_segment
      4 [] (dest_list (candle_disjunctive_case16594_compact_token_plan ())) in
  let raw =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_prove_six
      prepared cells in
  let initial_stack =
    candle_q_dim_taylor_model_fixed_outer_variable_compact_initial_six
      prepared in
  let initial_state =
    {tokenwise_jobs_term = raw.variable_raw_decoded_jobs_term;
     tokenwise_jobs_accept_theorem = raw.variable_raw_accept_theorem;
     tokenwise_stack_term = initial_stack.variable_compact_state_stack_term;
     tokenwise_stack_pass_theorem =
       initial_stack.variable_compact_state_pass_theorem} in
  let rec consume index state = function
    | [] -> state
    | token :: tokens ->
        consume (index + 1)
          (candle_disjunctive_case16594_tokenwise_step
            prepared index state token)
          tokens in
  let final_state = consume 0 initial_state segment_items in
  let active_roots = length (dest_list final_state.tokenwise_stack_term) in
  let axioms_after = axioms () in
  if length cells <> 4 || length segment_items <> 7 ||
     remaining_tokens = [] || dest_list final_state.tokenwise_jobs_term <> [] ||
     active_roots <> 1 ||
     hyp final_state.tokenwise_jobs_accept_theorem <> [] ||
     hyp final_state.tokenwise_stack_pass_theorem <> [] ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case16594 tokenwise prefix4: validation failed";
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_CASE16594_TOKENWISE_PREFIX4_RESULT" ^
     " numerical_cells=4 token_steps=7 active_roots=" ^
     string_of_int active_roots ^ " assumptions=0");
  print_endline
    "CANDLE_CV_DISJUNCTIVE_CASE16594_TOKENWISE_PREFIX4_OK DEVELOPMENT_NON_RELEASE";;

end;;
