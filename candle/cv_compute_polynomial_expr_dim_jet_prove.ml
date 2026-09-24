(* ========================================================================== *)
(* Proof-producing shared-jet checks for six-dimensional polynomial boxes.   *)
(*                                                                            *)
(* A source function is reified and compiled once.  Each subsequent exact    *)
(* rational box is evaluated as ordinary data and connected to the universal *)
(* shared-jet soundness theorem.                                               *)
(* ========================================================================== *)

needs "candle/compute.ml";;
needs "candle/cv_compute_exact_interval_reify.ml";;
needs "candle/cv_compute_polynomial_expr_flyspeck_fixture.ml";;
needs "candle/cv_compute_polynomial_expr_dim_jet_sound.ml";;

module Candle_cv_polynomial_expr_dim_jet_prove = struct

open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_flyspeck_reify;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_first_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_check;;
open Candle_cv_polynomial_expr_dim_jet_sound;;

type candle_q_dim_poly_jet_prepared_six = {
  function_term : term;
  vector_term : term;
  source_term : term;
  expression_term : term;
  valid_theorem : thm;
  source_theorem : thm;
  program_term : term;
  compile_theorem : thm;
  program_representation : thm;
  program_representation_term : term;
};;

let candle_q_dim_poly_jet_program_encode_conv program =
  REWRITE_CONV
    [candle_cv_q_instruction_list_def; candle_cv_q_instruction_def;
     candle_cv_q_def; candle_cv_lc_z_def]
    (mk_comb (`candle_cv_q_instruction_list`,program));;

let candle_q_dim_poly_jet_boxes_encode_conv boxes =
  REWRITE_CONV
    [candle_cv_q_interval_list_def; candle_cv_q_interval_def;
     candle_cv_q_def; candle_cv_lc_z_def]
    (mk_comb (`candle_cv_q_interval_list`,boxes));;

let candle_q_dim_poly_jet_dest_pair tm =
  let partial,right = dest_comb tm in
  let operator,left = dest_comb partial in
  if aconv operator `Cexp_pair` then left,right
  else failwith "shared-jet prover: final result is not a pair";;

let candle_q_dim_poly_jet_flag_accept = prove
 (`!b. (1:num) = (if b then 1 else 0) ==> b`,
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_q_dim_poly_jet_suc_one = SYM ONE;;
let candle_q_dim_poly_jet_dim_six = DIMINDEX_CONV `dimindex (:6)`;;
let candle_q_dim_poly_jet_sound_six =
  REWRITE_RULE
    [candle_q_dim_poly_jet_dim_six]
    (INST_TYPE
      [`:6`,`:N`]
      candle_q_dim_poly_jet_whole_box_accept_sound);;

let candle_q_dim_poly_jet_prepare_six function_tm =
  let vector,source = dest_abs function_tm in
  if type_of vector <> `:real^6` || type_of source <> `:real` then
    failwith "shared-jet prover: expected real^6 -> real source";
  let expression,valid,source_theorem,program,run_theorem =
    candle_poly_reify_vector_expression vector source in
  let compile_theorem =
    REWRITE_CONV [candle_poly_compile_def; APPEND]
      (mk_comb (`candle_poly_compile`,expression)) in
  if not (aconv (rand (concl compile_theorem)) program) then
    failwith "shared-jet prover: compiler/reifier program mismatch";
  let program_representation =
    candle_q_dim_poly_jet_program_encode_conv program in
  if hyp valid <> [] || hyp source_theorem <> [] ||
     hyp run_theorem <> [] || hyp compile_theorem <> [] ||
     hyp program_representation <> [] then
    failwith "shared-jet prover: prepared source has assumptions";
  {
    function_term = function_tm;
    vector_term = vector;
    source_term = source;
    expression_term = expression;
    valid_theorem = valid;
    source_theorem = source_theorem;
    program_term = program;
    compile_theorem = compile_theorem;
    program_representation = program_representation;
    program_representation_term = rand (concl program_representation);
  };;

let candle_q_dim_poly_jet_compute equations tm =
  let th = compute equations tm in
  if hyp th <> [] then
    failwith "shared-jet prover: computed theorem has assumptions";
  th;;

let candle_q_dim_poly_jet_prove_box_six prepared lower upper =
  if length lower <> 6 || length upper <> 6 then
    failwith "shared-jet prover: expected six box coordinates";
  let boxes = candle_poly_fixture_q_boxes lower upper in
  let boxes_representation =
    candle_q_dim_poly_jet_boxes_encode_conv boxes in
  let boxes_representation_term =
    rand (concl boxes_representation) in

  let center_environment_theorem =
    candle_q_dim_poly_jet_compute
      candle_cv_q_dim_first_jet_compute_eqs
      (mk_comb
        (`candle_cv_q_center_environment_list`,
         boxes_representation_term)) in
  let center_environment =
    rand (concl center_environment_theorem) in

  let center_theorem =
    candle_q_dim_poly_jet_compute
      candle_cv_q_dim_first_jet_compute_eqs
      (list_mk_comb
        (`candle_cv_q_dim_first_jet_program`,
         [center_environment;prepared.program_representation_term])) in
  let center = rand (concl center_theorem) in

  let box_theorem =
    candle_q_dim_poly_jet_compute
      candle_cv_q_dim_first_jet_compute_eqs
      (list_mk_comb
        (`candle_cv_q_dim_jet_program`,
         [boxes_representation_term;
          prepared.program_representation_term])) in
  let box = rand (concl box_theorem) in

  let upper_theorem =
    candle_q_dim_poly_jet_compute
      (candle_cv_q_dim_first_jet_compute_eqs @
       [SPEC_ALL candle_cv_q_jet_upper_pair_def])
      (list_mk_comb
        (`candle_cv_q_jet_upper_pair`,
         [boxes_representation_term;center;box])) in
  let upper = rand (concl upper_theorem) in

  let valid_theorem =
    candle_q_dim_poly_jet_compute
      candle_cv_q_dim_first_jet_compute_eqs
      (mk_comb (`candle_cv_q_box_valid_list`,
                boxes_representation_term)) in
  let valid = rand (concl valid_theorem) in

  let finish_theorem =
    candle_q_dim_poly_jet_compute
      candle_cv_q_dim_first_jet_compute_eqs
      (list_mk_comb
        (`candle_cv_q_dim_whole_box_finish`,
         [`Cexp_num 1`;valid;upper])) in
  let finish = rand (concl finish_theorem) in
  let verdict,_ = candle_q_dim_poly_jet_dest_pair finish in
  if not (aconv verdict `Cexp_num 1`) then
    failwith "shared-jet prover: box rejected";

  let compute_tm =
    list_mk_comb
      (`candle_cv_q_dim_poly_jet_whole_box_check`,
       [prepared.program_representation_term;
        boxes_representation_term]) in
  let expansion_theorem =
    REWRITE_CONV
      [candle_cv_q_dim_poly_jet_whole_box_check_def;
       candle_cv_q_dim_poly_jet_whole_box_upper_def]
      compute_tm in
  let evaluation_theorem =
    REWRITE_CONV
      [center_environment_theorem;center_theorem;box_theorem;
       upper_theorem;valid_theorem;finish_theorem]
      (rand (concl expansion_theorem)) in
  let compute_theorem =
    TRANS expansion_theorem evaluation_theorem in
  let correctness =
    SPECL [prepared.expression_term;boxes]
      candle_cv_q_dim_poly_jet_whole_box_check_correct in
  let abstract_compute_theorem =
    let th =
      PURE_REWRITE_RULE
        [SYM prepared.program_representation;
         SYM boxes_representation]
        compute_theorem in
    PURE_REWRITE_RULE [SYM prepared.compile_theorem] th in
  if not
      (aconv (lhand (concl abstract_compute_theorem))
             (lhand (concl correctness))) then
    failwith "shared-jet prover: abstract checker mismatch";
  let accept_encoding_theorem =
    TRANS (SYM abstract_compute_theorem) correctness in
  let numerical_goal =
    list_mk_comb
      (`candle_q_dim_poly_jet_whole_box_numerical_accept`,
       [prepared.expression_term;boxes]) in
  let abstract_verdict_theorem =
    PURE_REWRITE_RULE [candle_q_dim_poly_jet_suc_one]
      (REWRITE_RULE [cexp_fst_def]
        (AP_TERM `Cexp_fst` accept_encoding_theorem)) in
  let computed_verdict_theorem =
    REWRITE_RULE [cexp_fst_def]
      (AP_TERM `Cexp_fst` finish_theorem) in
  if not
      (aconv (lhand (concl computed_verdict_theorem))
             (lhand (concl abstract_verdict_theorem))) then
    failwith "shared-jet prover: computed verdict mismatch";
  let verdict_theorem =
    TRANS (SYM computed_verdict_theorem) abstract_verdict_theorem in
  let flag_theorem =
    REWRITE_RULE [injectivity "cval"] verdict_theorem in
  let expected_flag =
    mk_eq (`1`,mk_cond (numerical_goal,`1`,`0`)) in
  let flag_theorem =
    if aconv (concl flag_theorem) expected_flag then flag_theorem
    else if aconv (concl flag_theorem)
              (mk_eq (rand expected_flag,lhand expected_flag)) then
      SYM flag_theorem
    else failwith "shared-jet prover: numerical flag mismatch" in
  let numerical_theorem =
    MATCH_MP
      (SPEC numerical_goal candle_q_dim_poly_jet_flag_accept)
      flag_theorem in
  let length_six =
    prove
      (mk_eq
        (mk_comb
          (`LENGTH:(((num#num)#num)#((num#num)#num))list->num`,
           boxes),
         `6`),
       REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV) in
  let vector_theorem =
    MATCH_MP
      (SPECL [prepared.expression_term;boxes]
        candle_q_dim_poly_jet_sound_six)
      (CONJ prepared.valid_theorem
        (CONJ length_six numerical_theorem)) in
  let source_theorem =
    REWRITE_RULE [prepared.source_theorem] vector_theorem in
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
    failwith "shared-jet prover: source theorem mismatch";
  source_theorem;;

end;;
