(* ========================================================================== *)
(* Proof-producing adapter for accepted jobs and a box-free topology stream. *)
(*                                                                            *)
(* Numerical acceptance may be proved in bounded independent batches.  This  *)
(* adapter checks only the compact postorder topology: leaf tokens consume   *)
(* jobs, while glue tokens reconstruct and immediately discharge one parent. *)
(* The final universal soundness theorem returns one source-level result.     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_stable_program_data.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_prove = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_tree_compact;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_sound;;

type candle_q_dim_taylor_model_fixed_outer_variable_compact_core_result_six = {
  variable_compact_core_stream_term : term;
  variable_compact_core_root_boxes_term : term;
  variable_compact_core_run_theorem : thm;
  variable_compact_core_source_theorem : thm;
};;

type candle_q_dim_taylor_model_fixed_outer_variable_compact_result_six = {
  variable_compact_raw_result :
    candle_q_dim_taylor_model_fixed_outer_variable_raw_result_six;
  variable_compact_stream_term : term;
  variable_compact_root_boxes_term : term;
  variable_compact_run_theorem : thm;
  variable_compact_source_theorem : thm;
};;

type candle_q_dim_taylor_model_fixed_outer_variable_compact_state_six = {
  variable_compact_state_stack_term : term;
  variable_compact_state_pass_theorem : thm;
};;

type candle_q_dim_taylor_model_fixed_outer_variable_compact_transition_six = {
  variable_compact_transition_remaining_jobs_term : term;
  variable_compact_transition_remaining_jobs_accept_theorem : thm;
  variable_compact_transition_state :
    candle_q_dim_taylor_model_fixed_outer_variable_compact_state_six;
};;

(* The logical runner stays dimension-polymorphic.  This six-dimensional
   adapter supplies proved reductions for the small closed numeral guards so
   rewriting selects one branch at a time instead of expanding both sides of
   every conditional in a large certificate. *)
let candle_q_dim_taylor_model_fixed_outer_variable_compact_num_rewrites_six =
  let zero = `0`
  and one = `1`
  and six = `6`
  and le = `(<=):num->num->bool`
  and suc = `SUC:num->num` in
  let rec successors count current =
    if count = 0 then []
    else current :: successors (count - 1) (mk_comb (suc,current)) in
  let rec concatenate = function
    | [] -> []
    | items :: remaining -> items @ concatenate remaining in
  let axes = map mk_small_numeral [1;2;3;4;5;6] in
  let currents = successors 6 one in
  let length_six =
    mk_eq (funpow 6 (fun value -> mk_comb (suc,value)) zero,six) in
  let bounds =
    concatenate
      (map
        (fun axis ->
          [list_mk_comb (le,[one;axis]);
           list_mk_comb (le,[axis;six])])
        axes) in
  let positions =
    concatenate
      (map
        (fun current -> map (fun axis -> mk_eq (current,axis)) axes)
        currents) in
  map NUM_REDUCE_CONV (length_six :: bounds @ positions);;

let candle_q_dim_taylor_model_fixed_outer_variable_compact_initial_six
    (prepared:candle_q_dim_analytic_jet_prepared_six) =
  let stack =
    `[]:((((num#num)#num)#((num#num)#num))list)list` in
  let pass =
    mk_icomb
      (mk_icomb
        (mk_icomb
          (`candle_q_dim_taylor_model_fixed_outer_variable_compact_stack_pass`,
           `ARB:real^6`),
         prepared.expression_term),
       stack) in
  let theorem =
    EQT_ELIM
      (REWRITE_CONV
        [candle_q_dim_taylor_model_fixed_outer_variable_compact_stack_pass_def]
        pass) in
  {variable_compact_state_stack_term = stack;
   variable_compact_state_pass_theorem = theorem};;

(* Consume one already accepted bounded job batch and its matching postorder
   token segment.  Only the active root stack and its universal invariant
   survive the call; raw encodings, hint payloads, and batch theorems can be
   reclaimed before the next segment. *)
let candle_q_dim_taylor_model_fixed_outer_variable_compact_transition_six
    (prepared:candle_q_dim_analytic_jet_prepared_six)
    state jobs jobs_accept_theorem tokens =
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-step-validation-begin";
  let expected_acceptance =
    list_mk_comb
      (`candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept`,
       [prepared.expression_term;jobs]) in
  let expected_stack_pass =
    mk_icomb
      (mk_icomb
        (mk_icomb
          (`candle_q_dim_taylor_model_fixed_outer_variable_compact_stack_pass`,
           `ARB:real^6`),
         prepared.expression_term),
       state.variable_compact_state_stack_term) in
  if hyp jobs_accept_theorem <> [] ||
     not (aconv (concl jobs_accept_theorem) expected_acceptance) ||
     hyp state.variable_compact_state_pass_theorem <> [] ||
     not
       (aconv (concl state.variable_compact_state_pass_theorem)
         expected_stack_pass) then
    failwith "fixed outer variable compact step: premise mismatch";
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-step-validation-end";
  let run_call =
    mk_icomb
      (mk_icomb
        (mk_icomb
          (mk_icomb
            (`candle_q_dim_taylor_model_fixed_outer_variable_compact_run`,
             `6`),
           tokens),
         jobs),
       state.variable_compact_state_stack_term) in
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-step-reduction-begin";
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
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-step-reduction-end";
  let success,payload = dest_pair (rand (concl run_theorem)) in
  let remaining,final_stack = dest_pair payload in
  if not (aconv success `T`) then
    failwith "fixed outer variable compact step: token segment rejected";
  let soundness =
    REWRITE_RULE
      [candle_q_dim_analytic_jet_dim_six]
      (ISPECL
        [tokens;prepared.expression_term;`ARB:real^6`;jobs;
         state.variable_compact_state_stack_term;
         remaining;
         final_stack]
        candle_q_dim_taylor_model_fixed_outer_variable_compact_run_sound) in
  let premise =
    CONJ prepared.valid_theorem
      (CONJ jobs_accept_theorem
        (CONJ state.variable_compact_state_pass_theorem run_theorem)) in
  let conclusion = MATCH_MP soundness premise in
  let remaining_accept_theorem = CONJUNCT1 conclusion in
  let stack_pass_theorem = CONJUNCT2 conclusion in
  {variable_compact_transition_remaining_jobs_term = remaining;
   variable_compact_transition_remaining_jobs_accept_theorem =
     remaining_accept_theorem;
   variable_compact_transition_state =
     {variable_compact_state_stack_term = final_stack;
      variable_compact_state_pass_theorem = stack_pass_theorem}};;

let candle_q_dim_taylor_model_fixed_outer_variable_compact_step_six
    (prepared:candle_q_dim_analytic_jet_prepared_six)
    state jobs jobs_accept_theorem tokens =
  let transition =
    candle_q_dim_taylor_model_fixed_outer_variable_compact_transition_six
      prepared state jobs jobs_accept_theorem tokens in
  if dest_list
       transition.variable_compact_transition_remaining_jobs_term <> [] then
    failwith "fixed outer variable compact step: unconsumed jobs";
  transition.variable_compact_transition_state;;

let candle_q_dim_taylor_model_fixed_outer_variable_compact_finish_six
    (prepared:candle_q_dim_analytic_jet_prepared_six) state =
  let root_boxes =
    match dest_list state.variable_compact_state_stack_term with
    | [boxes] -> boxes
    | _ -> failwith "fixed outer variable compact finish: non-singleton stack" in
  let expanded =
    REWRITE_RULE
      [candle_q_dim_taylor_model_fixed_outer_variable_compact_stack_pass_def]
      state.variable_compact_state_pass_theorem in
  let cell_theorem =
    try CONJUNCT1 expanded with Failure _ -> expanded in
  let source_theorem =
    REWRITE_RULE [m_cell_pass;prepared.source_theorem] cell_theorem in
  if hyp source_theorem <> [] then
    failwith "fixed outer variable compact finish: source assumptions";
  root_boxes,source_theorem;;

let candle_q_dim_taylor_model_fixed_outer_variable_compact_acceptance_six
    (prepared:candle_q_dim_analytic_jet_prepared_six)
    jobs jobs_accept_theorem tokens =
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-acceptance-validation-begin";
  let expected_acceptance =
    list_mk_comb
      (`candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept`,
       [prepared.expression_term;jobs]) in
  if hyp jobs_accept_theorem <> [] ||
     not (aconv (concl jobs_accept_theorem) expected_acceptance) then
    failwith "fixed outer variable compact prover: acceptance mismatch";
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-acceptance-validation-end";
  let empty_stack =
    `[]:((((num#num)#num)#((num#num)#num))list)list` in
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-run-call-construction-begin";
  let run_call =
    mk_icomb
      (mk_icomb
        (mk_icomb
          (mk_icomb
            (`candle_q_dim_taylor_model_fixed_outer_variable_compact_run`,
             `6`),
           tokens),
         jobs),
       empty_stack) in
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-run-call-construction-end";
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-stack-reduction-begin";
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
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-stack-reduction-end";
  let reduced = rand (concl run_theorem) in
  let success,payload =
    try dest_pair reduced with Failure _ ->
      failwith
        ("fixed outer variable compact prover: non-pair reduction: " ^
         string_of_term reduced) in
  let remaining,stack = dest_pair payload in
  if not (aconv success `T`) || dest_list remaining <> [] then
    failwith
      ("fixed outer variable compact prover: stream rejected: success=" ^
       string_of_term success ^ " remaining=" ^ string_of_term remaining);
  let root_boxes =
    match dest_list stack with
    | [boxes] -> boxes
    | _ -> failwith "fixed outer variable compact prover: non-singleton stack" in
  let soundness =
    REWRITE_RULE
      [candle_q_dim_analytic_jet_dim_six]
      (ISPECL
        [prepared.expression_term;`ARB:real^6`;tokens;jobs;root_boxes]
        candle_q_dim_taylor_model_fixed_outer_variable_compact_sound) in
  let premise =
    CONJ prepared.valid_theorem
      (CONJ jobs_accept_theorem run_theorem) in
  if not (aconv (fst (dest_imp (concl soundness))) (concl premise)) then
    failwith "fixed outer variable compact prover: soundness premise mismatch";
  let cell_theorem = MATCH_MP soundness premise in
  let source_theorem =
    REWRITE_RULE [m_cell_pass;prepared.source_theorem] cell_theorem in
  if hyp source_theorem <> [] then
    failwith "fixed outer variable compact prover: source assumptions";
  {variable_compact_core_stream_term = tokens;
   variable_compact_core_root_boxes_term = root_boxes;
   variable_compact_core_run_theorem = run_theorem;
   variable_compact_core_source_theorem = source_theorem};;

let candle_q_dim_taylor_model_fixed_outer_variable_compact_source_six
    (raw_result:
      candle_q_dim_taylor_model_fixed_outer_variable_raw_result_six)
    tokens =
  let core =
    candle_q_dim_taylor_model_fixed_outer_variable_compact_acceptance_six
      raw_result.variable_raw_prepared_source
      raw_result.variable_raw_decoded_jobs_term
      raw_result.variable_raw_accept_theorem tokens in
  {variable_compact_raw_result = raw_result;
   variable_compact_stream_term = core.variable_compact_core_stream_term;
   variable_compact_root_boxes_term =
     core.variable_compact_core_root_boxes_term;
   variable_compact_run_theorem = core.variable_compact_core_run_theorem;
   variable_compact_source_theorem =
     core.variable_compact_core_source_theorem};;

print_endline
  "CANDLE_CV_FIXED_OUTER_VARIABLE_COMPACT_STACK_PROVE_OK DEVELOPMENT_NON_RELEASE";;

end;;
