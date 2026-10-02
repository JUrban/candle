(* ========================================================================== *)
(* Fail-closed tests for the precomputed complete-checker theorem handoff.    *)
(*                                                                            *)
(* These checks deliberately use a dummy prepared record.  Every rejected    *)
(* input must fail before the adapter consults any analytic proof in it.      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_complete_prove.ml";;

module Test_cv_compute_analytic_expr_complete_precomputed_handoff_reject = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_prove;;

let candle_complete_precomputed_reject_dummy_prepared =
  {function_term = `\x:real^6. &0`;
   vector_term = `x:real^6`;
   source_term = `&0:real`;
   expression_term = `T`;
   valid_theorem = REFL `T`;
   source_theorem = REFL `T`;
   program_term = `Cexp_num 0`;
   compile_theorem = REFL `T`;
   program_representation = REFL `T`;
   program_representation_term = `Cexp_num 0`};;

let candle_complete_precomputed_reject_leaf =
  `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf`;;

let candle_complete_precomputed_reject_tokens =
  mk_list
    ([candle_complete_precomputed_reject_leaf],
     type_of candle_complete_precomputed_reject_leaf);;

let candle_complete_precomputed_reject_encoded_tokens =
  candle_q_dim_stable_program_cval_pair `Cexp_num 0` `Cexp_num 0`;;

let candle_complete_precomputed_reject_encoded_jobs =
  candle_q_dim_stable_program_cval_pair `Cexp_num 0` `Cexp_num 0`;;

let candle_complete_precomputed_reject_call =
  list_mk_comb
    (`candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check`,
     [candle_complete_precomputed_reject_dummy_prepared.program_representation_term;
      `Cexp_num 6`;candle_complete_precomputed_reject_encoded_tokens;
      candle_complete_precomputed_reject_encoded_jobs]);;

let candle_complete_precomputed_reject_accepted_result =
  candle_q_dim_stable_program_cval_pair `Cexp_num 1`
    (candle_q_dim_stable_program_cval_pair `Cexp_num 1`
      (candle_q_dim_stable_program_cval_pair `Cexp_num 0` `Cexp_num 0`));;

let candle_complete_precomputed_rejects expected_message theorem =
  try
    let _ =
      candle_q_dim_taylor_model_fixed_outer_variable_complete_handoff_computed_stack_six
        candle_complete_precomputed_reject_dummy_prepared
        candle_complete_precomputed_reject_tokens
        candle_complete_precomputed_reject_encoded_tokens
        candle_complete_precomputed_reject_encoded_jobs theorem in
    false
  with Failure message -> message = expected_message;;

let _ =
  let axioms_before = axioms () in
  let rejected_compute =
    candle_q_dim_analytic_jet_compute
      (candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_compute_eqs ())
      candle_complete_precomputed_reject_call in
  let accepted_equation =
    mk_eq
      (candle_complete_precomputed_reject_call,
       candle_complete_precomputed_reject_accepted_result) in
  if not
       (candle_complete_precomputed_rejects
         "fixed outer complete checker: certificate rejected"
         rejected_compute) then
    failwith "complete precomputed handoff: rejected verdict was accepted";
  if not
       (candle_complete_precomputed_rejects
         "fixed outer complete checker: certificate rejected"
         (ASSUME accepted_equation)) then
    failwith "complete precomputed handoff: open theorem was accepted";
  if not
       (candle_complete_precomputed_rejects
         "fixed outer complete checker: certificate rejected"
         (REFL candle_complete_precomputed_reject_accepted_result)) then
    failwith "complete precomputed handoff: wrong computation was accepted";
  let token_mismatch_rejected =
    try
      let _ =
        candle_q_dim_taylor_model_fixed_outer_variable_complete_token_encoding
          candle_complete_precomputed_reject_tokens `Cexp_num 0` in
      false
    with Failure message ->
      message = "fixed outer complete checker: token encoding mismatch" in
  if not token_mismatch_rejected then
    failwith "complete precomputed handoff: token mismatch was accepted";
  let empty_rejected =
    try
      let empty_tokens =
        mk_list ([],type_of candle_complete_precomputed_reject_leaf) in
      let _ =
        candle_q_dim_taylor_model_fixed_outer_variable_complete_handoff_with_encoding_six
          candle_complete_precomputed_reject_dummy_prepared empty_tokens
          `Cexp_num 0` `Cexp_num 0` (REFL `Cexp_num 0`)
          (REFL candle_complete_precomputed_reject_accepted_result) in
      false
    with Failure message ->
      message = "fixed outer complete checker: empty certificate" in
  if not empty_rejected then
    failwith "complete precomputed handoff: empty certificate was accepted";
  let axioms_after = axioms () in
  if length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "complete precomputed handoff: axiom set changed";
  print_endline
    "CANDLE_CV_COMPLETE_PRECOMPUTED_HANDOFF_REJECT_OK DEVELOPMENT_NON_RELEASE";;

end;;
