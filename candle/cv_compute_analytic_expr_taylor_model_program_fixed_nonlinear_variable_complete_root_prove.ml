(* ========================================================================== *)
(* Root/source handoff for a computed fixed-nonlinear complete certificate.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_stable_program_data.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_root_prove = struct

open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_sound;;

type candle_q_dim_taylor_model_fixed_nonlinear_variable_complete_root_result_six = {
  fixed_nonlinear_variable_complete_root_encoded_term : term;
  fixed_nonlinear_variable_complete_root_boxes_term : term;
  fixed_nonlinear_variable_complete_root_compute_theorem : thm;
  fixed_nonlinear_variable_complete_root_cell_theorem : thm;
  fixed_nonlinear_variable_complete_root_source_theorem : thm;
};;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_complete_token_encoding
    tokens encoded_tokens =
  let token_call =
    mk_comb
      (`candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens`,
       tokens) in
  let token_encoding =
    REWRITE_CONV
      [candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens_def;
       candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_token_def]
      token_call in
  if hyp token_encoding <> [] ||
     not (aconv (lhand (concl token_encoding)) token_call) ||
     not (aconv (rand (concl token_encoding)) encoded_tokens) then
    failwith "fixed nonlinear complete root: token encoding mismatch";
  token_encoding;;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_complete_root_decode
    encoded_root =
  let call = mk_comb (`candle_cv_q_interval_list_decode`,encoded_root) in
  let theorem =
    REWRITE_CONV
      [candle_cv_q_interval_list_decode_def;
       candle_cv_q_interval_decode_def;candle_cv_q_decode_def;
       candle_cv_lc_z_decode_def;candle_cv_lc_num_decode_def;
       cexp_fst_def;cexp_snd_def;FST;SND]
      call in
  if hyp theorem <> [] || not (aconv (lhand (concl theorem)) call) then
    failwith "fixed nonlinear complete root: root decode mismatch";
  theorem;;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_complete_handoff_computed_root_six
    prepared tokens encoded_tokens encoded_jobs concrete_compute =
  let concrete_call =
    list_mk_comb
      (`candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_check`,
       [prepared.program_representation_term;`Cexp_num 6`;
        encoded_tokens;encoded_jobs]) in
  let numerical,topology =
    candle_q_dim_stable_program_dest_cval_pair
      "fixed nonlinear complete result" (rand (concl concrete_compute)) in
  let topology_success,topology_payload =
    candle_q_dim_stable_program_dest_cval_pair
      "fixed nonlinear complete topology" topology in
  let remaining_jobs,final_stack =
    candle_q_dim_stable_program_dest_cval_pair
      "fixed nonlinear complete payload" topology_payload in
  let encoded_root,encoded_tail =
    candle_q_dim_stable_program_dest_cval_pair
      "fixed nonlinear complete singleton root" final_stack in
  if hyp concrete_compute <> [] ||
     not (aconv (lhand (concl concrete_compute)) concrete_call) ||
     not (aconv numerical `Cexp_num 1`) ||
     not (aconv topology_success `Cexp_num 1`) ||
     not (aconv remaining_jobs `Cexp_num 0`) ||
     not (aconv encoded_tail `Cexp_num 0`) then
    failwith "fixed nonlinear complete root: certificate rejected";
  let token_encoding =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_complete_token_encoding
      tokens encoded_tokens in
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-variable-complete-root-handoff-begin";
  let source_program_encoding =
    TRANS
      (AP_TERM `candle_cv_analytic_instruction_list`
        prepared.compile_theorem)
      prepared.program_representation in
  let call_encoding =
    candle_q_dim_analytic_jet_congr_apps
      (REFL
        `candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_check`)
      [source_program_encoding;REFL `Cexp_num 6`;token_encoding;
       REFL encoded_jobs] in
  let abstract_compute = TRANS call_encoding concrete_compute in
  let soundness =
    REWRITE_RULE
      [candle_q_dim_analytic_jet_dim_six]
      (ISPECL
        [prepared.expression_term;`ARB:real^6`;tokens;encoded_jobs;
         encoded_root]
        candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_accept) in
  let premise = CONJ prepared.valid_theorem abstract_compute in
  if not (aconv (fst (dest_imp (concl soundness))) (concl premise)) then
    failwith "fixed nonlinear complete root: soundness premise mismatch";
  let encoded_cell_theorem = MP soundness premise in
  let root_decode =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_complete_root_decode
      encoded_root in
  let cell_theorem = REWRITE_RULE [root_decode] encoded_cell_theorem in
  let source_theorem =
    REWRITE_RULE [m_cell_pass;prepared.source_theorem] cell_theorem in
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-variable-complete-root-handoff-end";
  if hyp cell_theorem <> [] || hyp source_theorem <> [] then
    failwith "fixed nonlinear complete root: unexpected assumptions";
  {fixed_nonlinear_variable_complete_root_encoded_term = encoded_root;
   fixed_nonlinear_variable_complete_root_boxes_term = rand (concl root_decode);
   fixed_nonlinear_variable_complete_root_compute_theorem = concrete_compute;
   fixed_nonlinear_variable_complete_root_cell_theorem = cell_theorem;
   fixed_nonlinear_variable_complete_root_source_theorem = source_theorem};;

end;;
