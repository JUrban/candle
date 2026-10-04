(* ========================================================================== *)
(* Root/source handoff for the one-verdict complete certificate checker.      *)
(*                                                                            *)
(* The existing complete adapter recovers the universal compact-stack         *)
(* invariant.  A complete postorder certificate has a singleton encoded       *)
(* stack, so the stronger complete_accept theorem can recover its root cell    *)
(* directly.  This unit performs that final generic handoff without replaying  *)
(* numerical arithmetic or topology.                                          *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_complete_prove.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_root_prove = struct

open M_verifier;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_prove;;

type candle_q_dim_taylor_model_fixed_outer_variable_complete_root_result_six = {
  variable_complete_root_stack_result :
    candle_q_dim_taylor_model_fixed_outer_variable_complete_stack_result_six;
  variable_complete_root_encoded_term : term;
  variable_complete_root_boxes_term : term;
  variable_complete_root_cell_theorem : thm;
  variable_complete_root_source_theorem : thm;
};;

let candle_q_dim_taylor_model_fixed_outer_variable_complete_root_decode
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
    failwith "fixed outer complete root handoff: root decode mismatch";
  theorem;;

let candle_q_dim_taylor_model_fixed_outer_variable_complete_handoff_computed_root_six
    prepared tokens encoded_tokens encoded_jobs concrete_compute =
  let token_encoding =
    candle_q_dim_taylor_model_fixed_outer_variable_complete_token_encoding
      tokens encoded_tokens in
  let stack_result =
    candle_q_dim_taylor_model_fixed_outer_variable_complete_handoff_with_encoding_six
      prepared tokens encoded_tokens encoded_jobs token_encoding
      concrete_compute in
  let encoded_root,encoded_tail =
    candle_q_dim_stable_program_dest_cval_pair
      "complete reflected singleton root"
      stack_result.variable_complete_encoded_stack_term in
  if not (aconv encoded_tail `Cexp_num 0`) then
    failwith "fixed outer complete root handoff: non-singleton stack";
  candle_q_dim_analytic_jet_profile_event
    "variable-complete-root-handoff-begin";
  let source_program_encoding =
    TRANS
      (AP_TERM `candle_cv_analytic_instruction_list`
        prepared.compile_theorem)
      prepared.program_representation in
  let call_encoding =
    candle_q_dim_analytic_jet_congr_apps
      (REFL
        `candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check`)
      [source_program_encoding;REFL `Cexp_num 6`;token_encoding;
       REFL encoded_jobs] in
  let abstract_compute = TRANS call_encoding concrete_compute in
  let soundness =
    REWRITE_RULE
      [candle_q_dim_analytic_jet_dim_six]
      (ISPECL
        [prepared.expression_term;`ARB:real^6`;tokens;encoded_jobs;
         encoded_root]
        candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_accept) in
  let premise = CONJ prepared.valid_theorem abstract_compute in
  if not (aconv (fst (dest_imp (concl soundness))) (concl premise)) then
    failwith "fixed outer complete root handoff: soundness premise mismatch";
  let encoded_cell_theorem = MP soundness premise in
  let root_decode =
    candle_q_dim_taylor_model_fixed_outer_variable_complete_root_decode
      encoded_root in
  let cell_theorem = REWRITE_RULE [root_decode] encoded_cell_theorem in
  let source_theorem =
    REWRITE_RULE [m_cell_pass;prepared.source_theorem] cell_theorem in
  candle_q_dim_analytic_jet_profile_event
    "variable-complete-root-handoff-end";
  if hyp cell_theorem <> [] || hyp source_theorem <> [] then
    failwith "fixed outer complete root handoff: unexpected assumptions";
  {variable_complete_root_stack_result = stack_result;
   variable_complete_root_encoded_term = encoded_root;
   variable_complete_root_boxes_term = rand (concl root_decode);
   variable_complete_root_cell_theorem = cell_theorem;
   variable_complete_root_source_theorem = source_theorem};;

print_endline
  "CANDLE_CV_FIXED_OUTER_VARIABLE_COMPLETE_ROOT_PROVE_OK DEVELOPMENT_NON_RELEASE";;

end;;
