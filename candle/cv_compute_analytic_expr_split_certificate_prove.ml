(* ========================================================================== *)
(* Proof-producing adapter for separate center and whole-box certificates.    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_jet_prove.ml";;
needs "candle/cv_compute_analytic_expr_split_certificate_check.ml";;

module Candle_cv_analytic_expr_split_certificate_prove = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_split_certificate_check;;

let candle_q_dim_analytic_split_certificate_sound_six =
  REWRITE_RULE
    [candle_q_dim_analytic_jet_dim_six]
    (INST_TYPE
      [`:6`,`:N`]
      candle_q_dim_analytic_split_certificate_accept_sound);;

let candle_q_dim_analytic_split_certificate_prove_box_six
    center_prepared box_prepared lower upper =
  if length lower <> 6 || length upper <> 6 then
    failwith "analytic split-certificate prover: expected six coordinates";
  if not
      (aconv center_prepared.function_term box_prepared.function_term) then
    failwith "analytic split-certificate prover: source-function mismatch";
  let erased_center =
    mk_comb
      (`candle_analytic_erase_sqrt_certificates`,
       center_prepared.expression_term) in
  let erased_box =
    mk_comb
      (`candle_analytic_erase_sqrt_certificates`,
       box_prepared.expression_term) in
  let erasure_theorem =
    REWRITE_CONV
      [candle_analytic_erase_sqrt_certificates_def]
      (mk_eq (erased_center,erased_box)) in
  if hyp erasure_theorem <> [] ||
     rand (concl erasure_theorem) <> `T` then
    failwith "analytic split-certificate prover: erased source mismatch";
  let erasure_equality = EQT_ELIM erasure_theorem in
  let boxes = candle_poly_fixture_q_boxes lower upper in
  let boxes_representation =
    candle_q_dim_analytic_jet_boxes_encode_conv boxes in
  let boxes_representation_term = rand (concl boxes_representation) in
  let _ =
    candle_q_dim_analytic_jet_profile_event "split-boxes-encoded" in

  let center_environment_theorem =
    candle_q_dim_analytic_jet_compute
      candle_cv_q_dim_analytic_split_certificate_compute_eqs
      (mk_comb
        (`candle_cv_q_center_environment_list`,
         boxes_representation_term)) in
  let center_environment = rand (concl center_environment_theorem) in
  let _ =
    candle_q_dim_analytic_jet_profile_event
      "split-center-environment-computed" in

  let center_theorem =
    candle_q_dim_analytic_jet_compute
      candle_cv_q_dim_analytic_split_certificate_compute_eqs
      (list_mk_comb
        (`candle_cv_q_dim_analytic_first_program`,
         [center_environment;
          center_prepared.program_representation_term])) in
  let center = rand (concl center_theorem) in
  let _ =
    candle_q_dim_analytic_jet_profile_event
      "split-center-jet-computed" in

  let box_theorem =
    candle_q_dim_analytic_jet_compute
      candle_cv_q_dim_analytic_split_certificate_compute_eqs
      (list_mk_comb
        (`candle_cv_q_dim_analytic_program`,
         [boxes_representation_term;
          box_prepared.program_representation_term])) in
  let box = rand (concl box_theorem) in
  let _ =
    candle_q_dim_analytic_jet_profile_event "split-box-jet-computed" in

  let finish_theorem =
    candle_q_dim_analytic_jet_compute
      candle_cv_q_dim_analytic_split_certificate_compute_eqs
      (list_mk_comb
        (`candle_cv_q_dim_analytic_split_certificate_finish`,
         [boxes_representation_term;center;box])) in
  let finish = rand (concl finish_theorem) in
  let _ =
    candle_q_dim_analytic_jet_profile_event "split-finish-computed" in
  let verdict,upper = candle_q_dim_analytic_jet_dest_pair finish in
  if not (aconv verdict `Cexp_num 1`) then (
    let center_domain =
      rand
        (concl
          (candle_q_dim_analytic_jet_compute
            candle_cv_q_dim_analytic_split_certificate_compute_eqs
            (mk_comb
              (`candle_cv_q_dim_analytic_first_result_domain`,center)))) in
    let box_domain =
      rand
        (concl
          (candle_q_dim_analytic_jet_compute
            candle_cv_q_dim_analytic_split_certificate_compute_eqs
            (mk_comb (`candle_cv_q_dim_analytic_result_domain`,box)))) in
    let box_valid =
      rand
        (concl
          (candle_q_dim_analytic_jet_compute
            candle_cv_q_dim_analytic_split_certificate_compute_eqs
            (mk_comb
              (`candle_cv_q_box_valid_list`,boxes_representation_term)))) in
    failwith
      ("analytic split-certificate prover: box rejected center_domain=" ^
       string_of_term center_domain ^ " box_domain=" ^
       string_of_term box_domain ^ " box_valid=" ^
       string_of_term box_valid ^ " upper=" ^ string_of_term upper));

  let compute_tm =
    list_mk_comb
      (`candle_cv_q_dim_analytic_split_certificate_check`,
       [center_prepared.program_representation_term;
        box_prepared.program_representation_term;
        boxes_representation_term]) in
  let expansion_theorem =
    REWRITE_CONV
      [candle_cv_q_dim_analytic_split_certificate_check_def]
      compute_tm in
  let center_call_theorem =
    TRANS
      (candle_q_dim_analytic_jet_congr_apps
        (REFL `candle_cv_q_dim_analytic_first_program`)
        [center_environment_theorem;
         REFL center_prepared.program_representation_term])
      center_theorem in
  let finish_call_theorem =
    TRANS
      (candle_q_dim_analytic_jet_congr_apps
        (REFL `candle_cv_q_dim_analytic_split_certificate_finish`)
        [REFL boxes_representation_term;
         center_call_theorem;box_theorem])
      finish_theorem in
  if not
      (aconv (lhand (concl finish_call_theorem))
             (rand (concl expansion_theorem))) then
    failwith "analytic split-certificate prover: evaluation mismatch";
  let compute_theorem =
    TRANS expansion_theorem finish_call_theorem in
  let correctness =
    SPECL
      [center_prepared.expression_term;
       box_prepared.expression_term;boxes]
      candle_cv_q_dim_analytic_split_certificate_check_correct in
  let center_program_encoding =
    TRANS
      (AP_TERM `candle_cv_analytic_instruction_list`
        center_prepared.compile_theorem)
      center_prepared.program_representation in
  let box_program_encoding =
    TRANS
      (AP_TERM `candle_cv_analytic_instruction_list`
        box_prepared.compile_theorem)
      box_prepared.program_representation in
  let call_encoding =
    candle_q_dim_analytic_jet_congr_apps
      (REFL `candle_cv_q_dim_analytic_split_certificate_check`)
      [center_program_encoding;box_program_encoding;boxes_representation] in
  let abstract_compute_theorem =
    TRANS call_encoding compute_theorem in
  if not
      (aconv (lhand (concl abstract_compute_theorem))
             (lhand (concl correctness))) then
    failwith "analytic split-certificate prover: abstract checker mismatch";
  let accept_encoding_theorem =
    TRANS (SYM abstract_compute_theorem) correctness in
  let base_numerical_goal =
    let center_domain =
      list_mk_comb
        (`candle_q_dim_analytic_domain`,
         [mk_comb (`candle_q_center_environment_list`,boxes);
          center_prepared.expression_term]) in
    let box_domain =
      list_mk_comb
        (`candle_q_dim_analytic_domain`,
         [boxes;box_prepared.expression_term]) in
    let upper =
      list_mk_comb
        (`candle_q_dim_analytic_split_certificate_upper`,
         [center_prepared.expression_term;
          box_prepared.expression_term;boxes]) in
    list_mk_conj
      [mk_comb (`candle_q_box_valid_list`,boxes);
       center_domain;box_domain;
       mk_neg (list_mk_comb (`candle_q_le`,[`candle_q_zero`;upper]))] in
  let flag_theorem =
    let th =
      REWRITE_RULE[cexp_fst_def; injectivity "cval"; SYM ONE]
        (AP_TERM `Cexp_fst` accept_encoding_theorem) in
    let expected =
      mk_eq (`1`,mk_cond (base_numerical_goal,`1`,`0`)) in
    if aconv (concl th) expected then th
    else if aconv (concl th) (mk_eq (rand expected,lhand expected)) then
      SYM th
    else failwith "analytic split-certificate prover: flag mismatch" in
  let base_numerical_theorem =
    MATCH_MP
      (SPEC base_numerical_goal candle_q_dim_analytic_jet_flag_accept)
      flag_theorem in
  let numerical_goal =
    list_mk_comb
      (`candle_q_dim_analytic_split_certificate_accept`,
       [center_prepared.expression_term;
        box_prepared.expression_term;boxes]) in
  let numerical_theorem =
    prove
      (numerical_goal,
       REWRITE_TAC
         [candle_q_dim_analytic_split_certificate_accept_def;
          erasure_equality] THEN
       ACCEPT_TAC base_numerical_theorem) in
  let length_six =
    prove
      (mk_eq
        (mk_comb
          (`LENGTH:(((num#num)#num)#((num#num)#num))list->num`,boxes),
         `6`),
       REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV) in
  let vector_theorem =
    MATCH_MP
      (SPECL
        [center_prepared.expression_term;
         box_prepared.expression_term;boxes]
        candle_q_dim_analytic_split_certificate_sound_six)
      (CONJ box_prepared.valid_theorem
        (CONJ length_six numerical_theorem)) in
  let source_theorem =
    REWRITE_RULE [box_prepared.source_theorem] vector_theorem in
  let point,body = dest_forall (concl source_theorem) in
  let _,claim = dest_imp body in
  let partial,zero = dest_comb claim in
  let relation,source_at_point = dest_comb partial in
  let expected_source =
    vsubst [point,box_prepared.vector_term] box_prepared.source_term in
  if hyp compute_theorem <> [] || hyp erasure_equality <> [] ||
     hyp numerical_theorem <> [] || hyp vector_theorem <> [] ||
     hyp source_theorem <> [] ||
     not (aconv relation `(<):real->real->bool`) ||
     not (aconv zero `&0:real`) ||
     not (aconv source_at_point expected_source) ||
     not (aconv (mk_abs (point,source_at_point))
                box_prepared.function_term) then
    failwith "analytic split-certificate prover: source theorem mismatch";
  source_theorem;;

end;;
