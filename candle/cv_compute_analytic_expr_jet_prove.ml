(* ========================================================================== *)
(* Proof-producing analytic shared-jet checks for six-dimensional boxes.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  A source function is reified once.  Polynomial *)
(* regions remain compact shared-jet instructions inside the analytic AST;    *)
(* each exact box is then checked as data and discharged by the universal     *)
(* analytic Taylor theorem.                                                   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_first_center_check.ml";;
needs "candle/cv_compute_polynomial_expr_flyspeck_fixture.ml";;

module Candle_cv_analytic_expr_jet_prove = struct

open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_flyspeck_reify;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_jet_check;;
open Candle_cv_analytic_expr_first_jet_program_compute;;
open Candle_cv_analytic_expr_first_center_check;;

type candle_q_dim_analytic_jet_prepared_six = {
  function_term : term;
  vector_term : term;
  source_term : term;
  polynomial_term : term;
  expression_term : term;
  valid_theorem : thm;
  source_theorem : thm;
  polynomial_program_term : term;
  program_term : term;
  compile_theorem : thm;
  program_representation : thm;
  program_representation_term : term;
};;

let candle_q_dim_analytic_jet_profile = ref (fun (_:string) -> ());;

let candle_q_dim_analytic_jet_profile_event event =
  (!candle_q_dim_analytic_jet_profile) event;;

let candle_q_dim_analytic_jet_program_encode_conv program =
  REWRITE_CONV
    [candle_cv_analytic_instruction_list_def;
     candle_cv_analytic_instruction_def;
     candle_cv_q_instruction_list_def; candle_cv_q_instruction_def;
     candle_cv_q_def; candle_cv_lc_z_def; FST; SND]
    (mk_comb (`candle_cv_analytic_instruction_list`,program));;

let candle_q_dim_analytic_jet_boxes_encode_conv boxes =
  REWRITE_CONV
    [candle_cv_q_interval_list_def; candle_cv_q_interval_def;
     candle_cv_q_def; candle_cv_lc_z_def; FST; SND]
    (mk_comb (`candle_cv_q_interval_list`,boxes));;

let candle_q_dim_analytic_jet_dest_pair tm =
  let partial,right = dest_comb tm in
  let operator,left = dest_comb partial in
  if aconv operator `Cexp_pair` then left,right
  else failwith "analytic shared-jet prover: final result is not a pair";;

let candle_q_dim_analytic_jet_flag_accept = prove
 (`!b. (1:num) = (if b then 1 else 0) ==> b`,
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_q_dim_analytic_jet_dim_six = DIMINDEX_CONV `dimindex (:6)`;;

let candle_q_dim_analytic_jet_sound_six =
  REWRITE_RULE
    [candle_q_dim_analytic_jet_dim_six]
    (INST_TYPE
      [`:6`,`:N`]
      candle_q_dim_analytic_jet_whole_box_accept_sound);;

let candle_q_dim_analytic_jet_prepare_six function_tm =
  let vector,source = dest_abs function_tm in
  if type_of vector <> `:real^6` || type_of source <> `:real` then
    failwith "analytic shared-jet prover: expected real^6 -> real source";
  let polynomial,polynomial_valid,polynomial_source,polynomial_program,
      polynomial_run =
    candle_poly_reify_vector_expression vector source in
  let expression = mk_comb (`Candle_analytic_poly`,polynomial) in
  let valid = prove
    (list_mk_comb
      (`candle_analytic_valid_dim`,[`6`;expression]),
     REWRITE_TAC[candle_analytic_valid_dim_def] THEN
     ACCEPT_TAC polynomial_valid) in
  let polynomial_bridge =
    MATCH_MP
      (ISPEC polynomial
        (REWRITE_RULE
          [candle_q_dim_analytic_jet_dim_six]
          (INST_TYPE [`:6`,`:N`] candle_analytic_denote_dim_poly)))
      polynomial_valid in
  let source_theorem =
    TRANS (AP_THM polynomial_bridge vector) polynomial_source in
  let compile_theorem =
    REWRITE_CONV
      [candle_analytic_compile_def; candle_poly_compile_def; APPEND]
      (mk_comb (`candle_analytic_compile`,expression)) in
  let program = rand (concl compile_theorem) in
  let program_representation =
    candle_q_dim_analytic_jet_program_encode_conv program in
  if hyp polynomial_valid <> [] || hyp polynomial_source <> [] ||
     hyp polynomial_run <> [] || hyp valid <> [] ||
     hyp source_theorem <> [] || hyp compile_theorem <> [] ||
     hyp program_representation <> [] ||
     length (dest_list program) <> 1 then
    failwith "analytic shared-jet prover: prepared source mismatch";
  {
    function_term = function_tm;
    vector_term = vector;
    source_term = source;
    polynomial_term = polynomial;
    expression_term = expression;
    valid_theorem = valid;
    source_theorem = source_theorem;
    polynomial_program_term = polynomial_program;
    program_term = program;
    compile_theorem = compile_theorem;
    program_representation = program_representation;
    program_representation_term = rand (concl program_representation);
  };;

let candle_q_dim_analytic_jet_compute equations tm =
  let th = Kernel.compute (COMPUTE_INIT_THMS,equations) tm in
  if hyp th <> [] then
    failwith "analytic shared-jet prover: computed theorem has assumptions";
  th;;

let candle_q_dim_analytic_jet_prove_box_six prepared lower upper =
  if length lower <> 6 || length upper <> 6 then
    failwith "analytic shared-jet prover: expected six box coordinates";
  let boxes = candle_poly_fixture_q_boxes lower upper in
  let boxes_representation =
    candle_q_dim_analytic_jet_boxes_encode_conv boxes in
  let boxes_representation_term = rand (concl boxes_representation) in
  let _ = candle_q_dim_analytic_jet_profile_event "boxes-encoded" in

  let center_environment_theorem =
    candle_q_dim_analytic_jet_compute
      candle_cv_q_dim_analytic_first_center_compute_eqs
      (mk_comb
        (`candle_cv_q_center_environment_list`,
         boxes_representation_term)) in
  let center_environment = rand (concl center_environment_theorem) in
  let _ =
    candle_q_dim_analytic_jet_profile_event
      "center-environment-computed" in

  let center_theorem =
    candle_q_dim_analytic_jet_compute
      candle_cv_q_dim_analytic_first_center_compute_eqs
      (list_mk_comb
        (`candle_cv_q_dim_analytic_first_program`,
         [center_environment;prepared.program_representation_term])) in
  let center = rand (concl center_theorem) in
  let _ =
    candle_q_dim_analytic_jet_profile_event "center-jet-computed" in

  let box_theorem =
    candle_q_dim_analytic_jet_compute
      candle_cv_q_dim_analytic_first_center_compute_eqs
      (list_mk_comb
        (`candle_cv_q_dim_analytic_program`,
         [boxes_representation_term;
          prepared.program_representation_term])) in
  let box = rand (concl box_theorem) in
  let _ = candle_q_dim_analytic_jet_profile_event "box-jet-computed" in

  let domain_theorem =
    candle_q_dim_analytic_jet_compute
      candle_cv_q_dim_analytic_first_center_compute_eqs
      (list_mk_comb
        (`candle_cv_bool_and`,
         [mk_comb
           (`candle_cv_q_dim_analytic_first_result_domain`,center);
          mk_comb
           (`candle_cv_q_dim_analytic_result_domain`,box)])) in
  let domain = rand (concl domain_theorem) in
  let _ = candle_q_dim_analytic_jet_profile_event "domain-computed" in

  let upper_theorem =
    candle_q_dim_analytic_jet_compute
      candle_cv_q_dim_analytic_first_center_compute_eqs
      (list_mk_comb
        (`candle_cv_q_dim_analytic_first_center_upper_pair`,
         [boxes_representation_term;center;box])) in
  let upper = rand (concl upper_theorem) in
  let _ = candle_q_dim_analytic_jet_profile_event "upper-computed" in

  let valid_theorem =
    candle_q_dim_analytic_jet_compute
      candle_cv_q_dim_analytic_first_center_compute_eqs
      (mk_comb
        (`candle_cv_q_box_valid_list`,boxes_representation_term)) in
  let valid = rand (concl valid_theorem) in
  let _ =
    candle_q_dim_analytic_jet_profile_event "box-validity-computed" in

  let finish_theorem =
    candle_q_dim_analytic_jet_compute
      candle_cv_q_dim_analytic_first_center_compute_eqs
      (list_mk_comb
        (`candle_cv_q_dim_whole_box_finish`,
         [domain;valid;upper])) in
  let finish = rand (concl finish_theorem) in
  let _ = candle_q_dim_analytic_jet_profile_event "finish-computed" in
  let verdict,_ = candle_q_dim_analytic_jet_dest_pair finish in
  if not (aconv verdict `Cexp_num 1`) then
    failwith "analytic shared-jet prover: box rejected";

  let compute_tm =
    list_mk_comb
      (`candle_cv_q_dim_analytic_first_center_check`,
       [prepared.program_representation_term;
        boxes_representation_term]) in
  let expansion_theorem =
    REWRITE_CONV
      [candle_cv_q_dim_analytic_first_center_check_def;
       candle_cv_q_dim_analytic_first_center_finish_def]
      compute_tm in
  let _ = candle_q_dim_analytic_jet_profile_event "checker-expanded" in
  let evaluation_theorem =
    REWRITE_CONV
      [center_environment_theorem;center_theorem;box_theorem;
       domain_theorem;upper_theorem;valid_theorem;finish_theorem]
      (rand (concl expansion_theorem)) in
  let compute_theorem = TRANS expansion_theorem evaluation_theorem in
  let _ =
    candle_q_dim_analytic_jet_profile_event
      "checker-evaluation-linked" in
  let correctness =
    SPECL [prepared.expression_term;boxes]
      candle_cv_q_dim_analytic_first_center_check_correct in
  let _ =
    candle_q_dim_analytic_jet_profile_event
      "checker-correctness-instantiated" in
  let abstract_compute_theorem =
    let th =
      PURE_REWRITE_RULE
        [SYM prepared.program_representation;
         SYM boxes_representation]
        compute_theorem in
    PURE_REWRITE_RULE [SYM prepared.compile_theorem] th in
  let _ =
    candle_q_dim_analytic_jet_profile_event
      "checker-representation-abstracted" in
  if not
      (aconv (lhand (concl abstract_compute_theorem))
             (lhand (concl correctness))) then
    failwith "analytic shared-jet prover: abstract checker mismatch";
  let accept_encoding_theorem =
    TRANS (SYM abstract_compute_theorem) correctness in
  let numerical_goal =
    list_mk_comb
      (`candle_q_dim_analytic_jet_whole_box_numerical_accept`,
       [prepared.expression_term;boxes]) in
  let flag_theorem =
    let th =
      REWRITE_RULE[cexp_fst_def; injectivity "cval"; SYM ONE]
        (AP_TERM `Cexp_fst` accept_encoding_theorem) in
    let expected =
      mk_eq (`1`,mk_cond (numerical_goal,`1`,`0`)) in
    if aconv (concl th) expected then th
    else if aconv (concl th)
              (mk_eq (rand expected,lhand expected)) then
      SYM th
    else failwith "analytic shared-jet prover: numerical flag mismatch" in
  let numerical_theorem =
    MATCH_MP
      (SPEC numerical_goal candle_q_dim_analytic_jet_flag_accept)
      flag_theorem in
  let _ =
    candle_q_dim_analytic_jet_profile_event
      "numerical-acceptance-derived" in
  let length_six =
    prove
      (mk_eq
        (mk_comb
          (`LENGTH:(((num#num)#num)#((num#num)#num))list->num`,boxes),
         `6`),
       REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV) in
  let _ =
    candle_q_dim_analytic_jet_profile_event "box-length-derived" in
  let vector_theorem =
    MATCH_MP
      (SPECL [prepared.expression_term;boxes]
        candle_q_dim_analytic_jet_sound_six)
      (CONJ prepared.valid_theorem
        (CONJ length_six numerical_theorem)) in
  let _ =
    candle_q_dim_analytic_jet_profile_event "soundness-instantiated" in
  let source_theorem =
    REWRITE_RULE [prepared.source_theorem] vector_theorem in
  let _ = candle_q_dim_analytic_jet_profile_event "source-rewritten" in
  let point,body = dest_forall (concl source_theorem) in
  let _,claim = dest_imp body in
  let partial,zero = dest_comb claim in
  let relation,source_at_point = dest_comb partial in
  let expected_source =
    vsubst [point,prepared.vector_term] prepared.source_term in
  if hyp compute_theorem <> [] || hyp numerical_theorem <> [] ||
     hyp vector_theorem <> [] || hyp source_theorem <> [] ||
     not (aconv relation `(<):real->real->bool`) ||
     not (aconv zero `&0:real`) ||
     not (aconv source_at_point expected_source) ||
     not (aconv (mk_abs (point,source_at_point))
                prepared.function_term) then
    failwith "analytic shared-jet prover: source theorem mismatch";
  source_theorem;;

end;;
