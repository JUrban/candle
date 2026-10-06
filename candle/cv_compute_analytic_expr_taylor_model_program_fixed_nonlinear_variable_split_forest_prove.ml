(* Multi-root forest extraction for bounded split fixed-nonlinear batches.    *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_split_stack_prove.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_split_forest_prove = struct

open M_verifier;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_split_stack_prove;;

type candle_q_dim_taylor_model_fixed_nonlinear_variable_split_forest_result_six = {
  fixed_nonlinear_split_forest_stack_result :
    candle_q_dim_taylor_model_fixed_nonlinear_variable_split_stack_result_six;
  fixed_nonlinear_split_forest_root_boxes : term list;
  fixed_nonlinear_split_forest_source_theorems : thm list;
};;

let rec candle_q_dim_taylor_model_fixed_nonlinear_variable_split_forest_aconv_lists
    left right =
  match left,right with
  | [],[] -> true
  | left_head::left_tail,right_head::right_tail ->
      aconv left_head right_head &&
      candle_q_dim_taylor_model_fixed_nonlinear_variable_split_forest_aconv_lists
        left_tail right_tail
  | _ -> false;;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_split_forest_decode
    encoded_stack =
  let call = mk_comb (`candle_cv_q_boxes_stack_decode`,encoded_stack) in
  let theorem =
    REWRITE_CONV
      [candle_cv_q_boxes_stack_decode_def;
       candle_cv_q_interval_list_decode_def;
       candle_cv_q_interval_decode_def;candle_cv_q_decode_def;
       candle_cv_lc_z_decode_def;candle_cv_lc_num_decode_def;
       cexp_fst_def;cexp_snd_def;FST;SND]
      call in
  if hyp theorem <> [] || not (aconv (lhand (concl theorem)) call) then
    failwith "fixed nonlinear split forest: stack decode mismatch";
  theorem;;

let rec candle_q_dim_taylor_model_fixed_nonlinear_variable_split_forest_cells
    count theorem =
  if count <= 0 then
    failwith "fixed nonlinear split forest: empty theorem extraction"
  else if count = 1 then [theorem]
  else
    CONJUNCT1 theorem ::
    candle_q_dim_taylor_model_fixed_nonlinear_variable_split_forest_cells
      (count - 1) (CONJUNCT2 theorem);;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_split_forest_six
    prepared raw_result tokens encoded_tokens expected_stack_boxes =
  if expected_stack_boxes = [] then
    failwith "fixed nonlinear split forest: empty expected stack";
  let stack_result =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_split_stack_six
      raw_result tokens encoded_tokens in
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-split-forest-extraction-begin";
  let stack_decode =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_split_forest_decode
      stack_result.fixed_nonlinear_split_encoded_stack_term in
  let root_boxes = dest_list (rand (concl stack_decode)) in
  if not
       (candle_q_dim_taylor_model_fixed_nonlinear_variable_split_forest_aconv_lists
         root_boxes expected_stack_boxes) then
    failwith "fixed nonlinear split forest: root box drift";
  let expanded_stack =
    REWRITE_RULE
      [stack_decode;
       candle_q_dim_taylor_model_fixed_outer_variable_compact_stack_pass_def]
      stack_result.fixed_nonlinear_split_stack_theorem in
  let cell_theorems =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_split_forest_cells
      (length root_boxes) expanded_stack in
  let source_theorems =
    map
      (fun theorem ->
        let source =
          REWRITE_RULE [m_cell_pass;prepared.source_theorem] theorem in
        if hyp theorem <> [] || hyp source <> [] then
          failwith "fixed nonlinear split forest: source assumptions";
        source)
      cell_theorems in
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-split-forest-extraction-end";
  {fixed_nonlinear_split_forest_stack_result = stack_result;
   fixed_nonlinear_split_forest_root_boxes = root_boxes;
   fixed_nonlinear_split_forest_source_theorems = source_theorems};;

print_endline
  "CANDLE_CV_FIXED_NONLINEAR_VARIABLE_SPLIT_FOREST_PROVE_OK DEVELOPMENT_NON_RELEASE";;

end;;
