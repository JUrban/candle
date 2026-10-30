(* ========================================================================== *)
(* Complete executable entry for certificate-driven packed source replay.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The executable entry runs the authenticated  *)
(* center and whole-box programs transactionally, requires singleton result *)
(* stacks and complete certificate consumption, authenticates the packed    *)
(* Hessian against the whole-box result, and applies the exact packed Taylor *)
(* acceptor.  Its soundness theorem retains the two logical source replays.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_packed_object_compute.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_certificate_dispatch_program_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_identity_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_entry_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_delta_neg_derivative_result_compute.ml";;

module Candle_cv_analytic_expr_packed_source_certificate_dispatch_entry_sound = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_packed_object_compute;;
open Candle_cv_analytic_expr_packed_source_item_invariant;;
open Candle_cv_analytic_expr_packed_source_certificate_step_compute;;
open Candle_cv_analytic_expr_packed_source_certificate_program_sound;;
open Candle_cv_analytic_expr_packed_source_certificate_dispatch_compute;;
open Candle_cv_analytic_expr_packed_source_certificate_dispatch_sound;;
open Candle_cv_analytic_expr_packed_source_certificate_dispatch_program_sound;;
open Candle_cv_analytic_expr_packed_source_identity_sound;;
open Candle_cv_analytic_expr_packed_source_object_entry_sound;;
open Candle_cv_analytic_expr_packed_source_delta_neg_derivative_result_compute;;

(* A completed program state has status one, exactly one stack value, and no *)
(* unconsumed certificate.  This predicate is used only in the proof layer;  *)
(* the executable check below is entirely cval-shaped.                       *)

let candle_q_packed_source_certificate_dispatch_state_complete_def =
  new_definition
 `candle_q_packed_source_certificate_dispatch_state_complete state <=>
    Cexp_fst state = Cexp_num 1 /\
    (?result.
       Cexp_fst (Cexp_snd state) = Cexp_pair result (Cexp_num 0)) /\
    Cexp_snd (Cexp_snd state) = Cexp_num 0`;;

let candle_cv_ispair_correct = prove
 (`!value.
     Cexp_ispair value =
     candle_cv_bool (?left right. value = Cexp_pair left right)`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `value:cval` (cases "cval")) THEN
  REWRITE_TAC[cexp_ispair_def; candle_cv_bool_def;
              distinctness "cval"; injectivity "cval"] THEN
  CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[]);;

let candle_cv_equal_correct = prove
 (`!left right.
     Cexp_eq left right = candle_cv_bool (left = right)`,
  REWRITE_TAC[cexp_eq_def; candle_cv_bool_def]);;

let candle_cv_q_packed_source_certificate_dispatch_state_complete_def =
  new_definition
 `candle_cv_q_packed_source_certificate_dispatch_state_complete state =
    candle_cv_bool_and
      (Cexp_eq (Cexp_fst state) (Cexp_num 1))
      (candle_cv_bool_and
        (Cexp_ispair (Cexp_fst (Cexp_snd state)))
        (candle_cv_bool_and
          (Cexp_eq
            (Cexp_snd (Cexp_fst (Cexp_snd state))) (Cexp_num 0))
          (Cexp_eq (Cexp_snd (Cexp_snd state)) (Cexp_num 0))))`;;

let candle_cval_pair_zero_tail = prove
 (`!value.
     ((?left right. value = Cexp_pair left right) /\
      Cexp_snd value = Cexp_num 0) <=>
     (?result. value = Cexp_pair result (Cexp_num 0))`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `value:cval` (cases "cval")) THEN
  REWRITE_TAC[cexp_snd_def; distinctness "cval"; injectivity "cval"] THEN
  MESON_TAC[]);;

let candle_state_complete_conjunction = prove
 (`!a b c d e.
     (b /\ c <=> e)
     ==> (a /\ b /\ c /\ d <=> a /\ e /\ d)`,
  MESON_TAC[]);;

let candle_cv_q_packed_source_certificate_dispatch_state_complete_correct =
  prove
 (`!state.
     candle_cv_q_packed_source_certificate_dispatch_state_complete state =
     candle_cv_bool
       (candle_q_packed_source_certificate_dispatch_state_complete state)`,
  GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_source_certificate_dispatch_state_complete_def;
     candle_q_packed_source_certificate_dispatch_state_complete_def;
     candle_cv_equal_correct; candle_cv_ispair_correct;
     candle_cv_bool_and_correct] THEN
  AP_TERM_TAC THEN
  MATCH_MP_TAC candle_state_complete_conjunction THEN
  MATCH_ACCEPT_TAC
    (SPEC `Cexp_fst (Cexp_snd state)` candle_cval_pair_zero_tail));;

(* Both dispatches share the exact authenticated source and plan.  The final *)
(* Hessian comparison is structural equality of the exact interval matrix,  *)
(* not a digest or producer assertion.                                       *)

let candle_cv_q_packed_source_certificate_dispatch_entry_def = new_definition
 `candle_cv_q_packed_source_certificate_dispatch_entry
      center_boxes outer_boxes codes sources
      center_certificates outer_certificates radii packed_hessian =
    let center_state =
      candle_cv_q_packed_source_certificate_dispatch_program
        center_boxes codes sources center_certificates (Cexp_num 0) in
    let outer_state =
      candle_cv_q_packed_source_certificate_dispatch_program
        outer_boxes codes sources outer_certificates (Cexp_num 0) in
    let center_result =
      Cexp_fst (Cexp_fst (Cexp_snd center_state)) in
    let outer_result =
      Cexp_fst (Cexp_fst (Cexp_snd outer_state)) in
    let complete =
      candle_cv_bool_and
        (candle_cv_q_packed_source_certificate_dispatch_state_complete
          center_state)
        (candle_cv_bool_and
          (candle_cv_q_packed_source_certificate_dispatch_state_complete
            outer_state)
          (Cexp_eq
            (candle_cv_q_packed_hessian6_expand packed_hessian)
            (candle_cv_q_dim_taylor_model_result_hessian outer_result))) in
    Cexp_if complete
      (candle_cv_q_packed_object_accept6
        (candle_cv_bool_and
          (candle_cv_q_dim_taylor_model_result_domain center_result)
          (candle_cv_q_dim_taylor_model_result_domain outer_result))
        radii
        (candle_cv_q_dim_taylor_model_result_value_bound center_result)
        (candle_cv_q_dim_taylor_model_result_gradient_bounds center_result)
        packed_hessian)
      (Cexp_num 0)`;;

let candle_cv_guarded_accept_one = prove
 (`!guard accepted.
     Cexp_if (candle_cv_bool guard) accepted (Cexp_num 0) = Cexp_num 1 <=>
     guard /\ accepted = Cexp_num 1`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `guard:bool` THEN
  ASM_REWRITE_TAC[candle_cv_bool_def; cexp_if_def;
                  injectivity "cval"] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_q_packed_source_certificate_dispatch_entry_components = prove
 (`!center_boxes outer_boxes codes sources center_certificates
       outer_certificates radii packed_hessian.
     candle_cv_q_packed_source_certificate_dispatch_entry
       center_boxes outer_boxes codes sources
       center_certificates outer_certificates radii packed_hessian =
       Cexp_num 1
     ==>
     let center_state =
       candle_cv_q_packed_source_certificate_dispatch_program
         center_boxes codes sources center_certificates (Cexp_num 0) in
     let outer_state =
       candle_cv_q_packed_source_certificate_dispatch_program
         outer_boxes codes sources outer_certificates (Cexp_num 0) in
     candle_q_packed_source_certificate_dispatch_state_complete center_state /\
     candle_q_packed_source_certificate_dispatch_state_complete outer_state /\
     candle_cv_q_packed_hessian6_expand packed_hessian =
       candle_cv_q_dim_taylor_model_result_hessian
         (Cexp_fst (Cexp_fst (Cexp_snd outer_state))) /\
     candle_cv_q_packed_object_accept6
       (candle_cv_bool_and
         (candle_cv_q_dim_taylor_model_result_domain
           (Cexp_fst (Cexp_fst (Cexp_snd center_state))))
         (candle_cv_q_dim_taylor_model_result_domain
           (Cexp_fst (Cexp_fst (Cexp_snd outer_state)))))
       radii
       (candle_cv_q_dim_taylor_model_result_value_bound
         (Cexp_fst (Cexp_fst (Cexp_snd center_state))))
       (candle_cv_q_dim_taylor_model_result_gradient_bounds
         (Cexp_fst (Cexp_fst (Cexp_snd center_state))))
       packed_hessian = Cexp_num 1`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_source_certificate_dispatch_entry_def;
     LET_DEF; LET_END_DEF;
     candle_cv_q_packed_source_certificate_dispatch_state_complete_correct;
     candle_cv_equal_correct; candle_cv_bool_and_correct;
     candle_cv_guarded_accept_one] THEN
  MESON_TAC[]);;

(* Structural decoding needs no inverse for Taylor results: pair-vs-number   *)
(* shape alone proves that the logical result list is a singleton.           *)

let candle_cv_q_dim_taylor_model_result_list_encode_length = prove
 (`!results.
     candle_cv_list_length
       (candle_cv_q_dim_taylor_model_result_list_encode results) =
     Cexp_num (LENGTH results)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_q_dim_taylor_model_result_list_encode_def;
                candle_cv_list_length_def; LENGTH];
    ASM_REWRITE_TAC
      [candle_cv_q_dim_taylor_model_result_list_encode_def;
       candle_cv_list_length_def; LENGTH; cexp_add_def;
       ARITH_RULE `1 + n = SUC n`]]);;

let candle_list_length_one = prove
 (`!items:A list.
     LENGTH items = 1 <=> ?item. items = CONS item []`,
  GEN_TAC THEN
  REWRITE_TAC
    [ARITH_RULE `1 = SUC 0`; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  MESON_TAC[]);;

let candle_q_packed_source_result_list_singleton = prove
 (`!items encoded_result.
     candle_cv_q_dim_taylor_model_result_list_encode
       (candle_q_packed_source_item_results items) =
     Cexp_pair encoded_result (Cexp_num 0)
     ==>
     ?item. items = CONS item []`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (MP_TAC o AP_TERM `candle_cv_list_length`) THEN
  REWRITE_TAC
    [candle_cv_q_dim_taylor_model_result_list_encode_length;
     candle_q_packed_source_item_results_def; LENGTH_MAP;
     candle_cv_list_length_def; cexp_add_def; injectivity "cval"] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MESON_TAC[candle_list_length_one]);;

let candle_cv_q_interval_list_empty = prove
 (`!certificates.
     candle_cv_q_interval_list certificates = Cexp_num 0
     ==> certificates = []`,
  GEN_TAC THEN
  DISCH_THEN (MP_TAC o AP_TERM `candle_cv_list_length`) THEN
  REWRITE_TAC
    [candle_cv_interval_list_length_correct;
     candle_cv_list_length_def; injectivity "cval";
     LENGTH_EQ_NIL]);;

let candle_q_packed_source_certificate_dispatch_state_complete_shape = prove
 (`!items certificates.
     candle_q_packed_source_certificate_dispatch_state_complete
       (candle_cv_q_packed_source_certificate_state T
         (candle_cv_q_dim_taylor_model_result_list_encode
           (candle_q_packed_source_item_results items))
         (candle_cv_q_interval_list certificates))
     ==>
     ?item. items = CONS item [] /\ certificates = []`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_q_packed_source_certificate_dispatch_state_complete_def;
     candle_cv_q_packed_source_certificate_state_def;
     candle_cv_bool_def; cexp_fst_def; cexp_snd_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MESON_TAC
    [candle_q_packed_source_result_list_singleton;
     candle_cv_q_interval_list_empty]);;

let candle_q_packed_source_empty_stack_term,
    candle_cv_q_packed_source_certificate_dispatch_program_empty_success_exact,
    candle_q_packed_source_result_term,
    candle_q_packed_source_certificate_rest_term,
    candle_q_packed_source_item_term =
  let variables,_ =
    strip_forall
      (concl
        candle_cv_q_packed_source_certificate_dispatch_program_success_exact) in
  let stack_type = type_of (List.nth variables 4) in
  let certificate_type = type_of (List.nth variables 3) in
  let _,[item_type] = dest_type stack_type in
  let empty_stack = mk_list([],item_type) in
  let inputs,_ = chop_list 4 variables in
  empty_stack,
  GENL inputs
    (SPECL
      (inputs @ [empty_stack])
      candle_cv_q_packed_source_certificate_dispatch_program_success_exact),
  mk_var("result",stack_type),
  mk_var("certificate_rest",certificate_type),
  mk_var("item",item_type);;

let candle_cv_q_packed_source_certificate_dispatch_program_empty_cval_exact =
  REWRITE_RULE
    [candle_q_packed_source_item_results_def; MAP;
     candle_cv_q_dim_taylor_model_result_list_encode_def]
    candle_cv_q_packed_source_certificate_dispatch_program_empty_success_exact;;

let candle_q_packed_source_center_item_term =
  mk_var("center_item",type_of candle_q_packed_source_item_term);;

let candle_q_packed_source_outer_item_term =
  mk_var("outer_item",type_of candle_q_packed_source_item_term);;

let candle_q_packed_source_center_stack_term =
  mk_list
    ([candle_q_packed_source_center_item_term],
     type_of candle_q_packed_source_center_item_term);;

let candle_q_packed_source_outer_stack_term =
  mk_list
    ([candle_q_packed_source_outer_item_term],
     type_of candle_q_packed_source_outer_item_term);;

let candle_q_packed_source_center_result_term =
  mk_icomb
    (`candle_q_packed_source_item_result`,
     candle_q_packed_source_center_item_term);;

let candle_q_packed_source_outer_result_term =
  mk_icomb
    (`candle_q_packed_source_item_result`,
     candle_q_packed_source_outer_item_term);;

let candle_q_packed_source_center_domain_term =
  mk_icomb
    (`candle_q_dim_taylor_model_result_domain`,
     candle_q_packed_source_center_result_term);;

let candle_q_packed_source_outer_domain_term =
  mk_icomb
    (`candle_q_dim_taylor_model_result_domain`,
     candle_q_packed_source_outer_result_term);;

let candle_q_packed_source_center_value_term =
  mk_icomb
    (`candle_q_dim_taylor_model_result_value_bound`,
     candle_q_packed_source_center_result_term);;

let candle_q_packed_source_center_gradient_term =
  mk_icomb
    (`candle_q_dim_taylor_model_result_gradient_bounds`,
     candle_q_packed_source_center_result_term);;

let candle_q_packed_source_outer_value_term =
  mk_icomb
    (`candle_q_dim_taylor_model_result_value_bound`,
     candle_q_packed_source_outer_result_term);;

let candle_q_packed_source_outer_gradient_term =
  mk_icomb
    (`candle_q_dim_taylor_model_result_gradient_bounds`,
     candle_q_packed_source_outer_result_term);;

let candle_q_packed_source_outer_hessian_term =
  mk_icomb
    (`candle_q_dim_taylor_model_result_hessian`,
     candle_q_packed_source_outer_result_term);;

let candle_q_packed_source_dispatch_packed_hessian_term =
  `packed_hessian:(((num#num)#num)#((num#num)#num))list`;;

let candle_cv_q_packed_source_dispatch_packed_hessian_term =
  mk_icomb
    (`candle_cv_q_interval_list`,
     candle_q_packed_source_dispatch_packed_hessian_term);;

let candle_cv_q_packed_source_dispatch_expanded_hessian_term =
  mk_icomb
    (`candle_cv_q_packed_hessian6_expand`,
     candle_cv_q_packed_source_dispatch_packed_hessian_term);;

let candle_cv_q_packed_source_outer_hessian_matrix_term =
  mk_icomb
    (`candle_cv_q_interval_matrix`,
     candle_q_packed_source_outer_hessian_term);;

let candle_cv_q_packed_source_dispatch_hessian_encoding_equality_term =
  mk_eq
    (candle_cv_q_packed_source_dispatch_expanded_hessian_term,
     candle_cv_q_packed_source_outer_hessian_matrix_term);;

let candle_q_packed_source_center_expr_term =
  mk_icomb
    (`candle_q_packed_source_item_box_expr`,
     candle_q_packed_source_center_item_term);;

let candle_q_packed_source_outer_expr_term =
  mk_icomb
    (`candle_q_packed_source_item_box_expr`,
     candle_q_packed_source_outer_item_term);;

let candle_cv_q_packed_source_certificate_dispatch_program_complete_exact =
  prove
 (`!boxes codes sources certificates.
     candle_q_packed_source_planned_program_instructions codes sources /\
     candle_q_packed_source_certificate_dispatch_state_complete
       (candle_cv_q_packed_source_certificate_dispatch_program
         (candle_cv_q_interval_list boxes)
         (candle_cv_q_packed_source_plan_code_list codes)
         (candle_cv_analytic_instruction_list sources)
         (candle_cv_q_interval_list certificates) (Cexp_num 0))
     ==>
     ?item.
       candle_q_packed_source_planned_certificate_program_run
         boxes codes sources certificates [] (CONS item []) [] /\
       candle_cv_q_packed_source_certificate_dispatch_program
         (candle_cv_q_interval_list boxes)
         (candle_cv_q_packed_source_plan_code_list codes)
         (candle_cv_analytic_instruction_list sources)
         (candle_cv_q_interval_list certificates) (Cexp_num 0) =
       candle_cv_q_packed_source_certificate_state T
         (candle_cv_q_dim_taylor_model_result_list_encode
           [candle_q_packed_source_item_result item])
         (candle_cv_q_interval_list [])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2
      (LABEL_TAC "planned_program")
      (LABEL_TAC "complete_dispatch")) THEN
  SUBGOAL_THEN
   `?result certificate_rest.
      candle_q_packed_source_planned_certificate_program_run
        boxes codes sources certificates [] result certificate_rest /\
      candle_cv_q_packed_source_certificate_dispatch_program
        (candle_cv_q_interval_list boxes)
        (candle_cv_q_packed_source_plan_code_list codes)
        (candle_cv_analytic_instruction_list sources)
        (candle_cv_q_interval_list certificates) (Cexp_num 0) =
      candle_cv_q_packed_source_certificate_state T
        (candle_cv_q_dim_taylor_model_result_list_encode
          (MAP candle_q_packed_source_item_result result))
        (candle_cv_q_interval_list certificate_rest)`
   MP_TAC THENL
   [MATCH_MP_TAC
      candle_cv_q_packed_source_certificate_dispatch_program_empty_cval_exact THEN
    ASM_REWRITE_TAC
      [candle_cv_q_packed_source_certificate_success_def] THEN
    ASM_MESON_TAC
      [candle_q_packed_source_certificate_dispatch_state_complete_def];
    ALL_TAC] THEN
  DISCH_THEN
    (X_CHOOSE_THEN candle_q_packed_source_result_term
      (X_CHOOSE_THEN candle_q_packed_source_certificate_rest_term
        (CONJUNCTS_THEN2
          (LABEL_TAC "logical_run")
          (LABEL_TAC "execution")))) THEN
  MP_TAC
    (ISPECL
      [candle_q_packed_source_result_term;
       candle_q_packed_source_certificate_rest_term]
      candle_q_packed_source_certificate_dispatch_state_complete_shape) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[candle_q_packed_source_item_results_def] THEN
    USE_THEN "execution"
      (fun theorem -> REWRITE_TAC[GSYM theorem]) THEN
    USE_THEN "complete_dispatch" ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN
    (X_CHOOSE_THEN candle_q_packed_source_item_term STRIP_ASSUME_TAC) THEN
  EXISTS_TAC candle_q_packed_source_item_term THEN
  ASM_REWRITE_TAC
    [candle_q_packed_source_item_results_def; MAP] THEN
  ASM_MESON_TAC[]);;

let candle_cv_q_interval_list_injective = prove
 (`!left right.
     candle_cv_q_interval_list left = candle_cv_q_interval_list right <=>
     left = right`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN (MP_TAC o AP_TERM `candle_cv_q_interval_list_decode`) THEN
    REWRITE_TAC[candle_cv_q_interval_list_roundtrip];
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

let candle_cv_q_interval_matrix_injective = prove
 (`!left right.
     candle_cv_q_interval_matrix left = candle_cv_q_interval_matrix right <=>
     left = right`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [GEN_TAC THEN
    STRUCT_CASES_TAC
      (ISPEC
        `right:((((num#num)#num)#((num#num)#num))list)list`
        list_CASES) THEN
    REWRITE_TAC[candle_cv_q_interval_matrix_def;
                distinctness "cval"; injectivity "cval"] THEN
    MESON_TAC[NOT_CONS_NIL];
    REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    STRUCT_CASES_TAC
      (ISPEC
        `right:((((num#num)#num)#((num#num)#num))list)list`
        list_CASES) THEN
    ASM_REWRITE_TAC[candle_cv_q_interval_matrix_def;
                   distinctness "cval"; injectivity "cval";
                   candle_cv_q_interval_list_injective; CONS_11] THEN
    MESON_TAC[NOT_CONS_NIL]]);;

(* This is the exact production-side contract: it retains both complete     *)
(* source/certificate replays and uses the same unrounded exact packed       *)
(* acceptor that the executable entry calls.                                 *)

let candle_q_packed_source_certificate_dispatch_accept_contract_def =
  new_definition
 `candle_q_packed_source_certificate_dispatch_accept_contract
      source_boxes center_boxes outer_boxes radii sources
      center_certificates outer_certificates center_item outer_item
      packed_hessian <=>
    LENGTH source_boxes = 6 /\
    LENGTH center_boxes = 6 /\
    LENGTH outer_boxes = 6 /\
    candle_q_box_valid_list center_boxes /\
    candle_q_box_valid_list outer_boxes /\
    candle_q_packed_source_correspondence
      source_boxes center_boxes outer_boxes radii /\
    candle_q_packed_source_certificate_program_run
      center_boxes sources center_certificates [] (CONS center_item []) [] /\
    candle_q_packed_source_certificate_program_run
      outer_boxes sources outer_certificates [] (CONS outer_item []) [] /\
    candle_analytic_erase_sqrt_certificates
      (candle_q_packed_source_item_box_expr center_item) =
      candle_analytic_erase_sqrt_certificates
        (candle_q_packed_source_item_box_expr outer_item) /\
    candle_q_packed_hessian6_expand packed_hessian =
      candle_q_dim_taylor_model_result_hessian
        (candle_q_packed_source_item_result outer_item) /\
    candle_cv_q_packed_object_accept6
      (candle_cv_bool
        (candle_q_dim_taylor_model_result_domain
           (candle_q_packed_source_item_result center_item) /\
         candle_q_dim_taylor_model_result_domain
           (candle_q_packed_source_item_result outer_item)))
      (candle_cv_q_list radii)
      (candle_cv_q_interval
        (candle_q_dim_taylor_model_result_value_bound
          (candle_q_packed_source_item_result center_item)))
      (candle_cv_q_interval_list
        (candle_q_dim_taylor_model_result_gradient_bounds
          (candle_q_packed_source_item_result center_item)))
      (candle_cv_q_interval_list packed_hessian) = Cexp_num 1`;;

let candle_q_packed_source_certificate_dispatch_accept_contract_cell_pass =
  prove
 (`!source_boxes center_boxes outer_boxes radii sources
       center_certificates outer_certificates center_item outer_item
       packed_hessian.
     candle_q_packed_source_certificate_dispatch_accept_contract
       source_boxes center_boxes outer_boxes radii sources
       center_certificates outer_certificates center_item outer_item
       packed_hessian
     ==>
     m_cell_pass
       (candle_analytic_denote_dim
         (candle_q_packed_source_item_box_expr outer_item))
       ((candle_q_box_lower_vector source_boxes:real^6),
        (candle_q_box_upper_vector source_boxes:real^6))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_q_packed_source_certificate_dispatch_accept_contract_def] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC
    (ISPECL
      [`source_boxes:(((num#num)#num)#((num#num)#num))list`;
       `center_boxes:(((num#num)#num)#((num#num)#num))list`;
       `outer_boxes:(((num#num)#num)#((num#num)#num))list`;
       `radii:((num#num)#num)list`;
       mk_conj
         (candle_q_packed_source_center_domain_term,
          candle_q_packed_source_outer_domain_term);
       candle_q_packed_source_center_value_term;
       candle_q_packed_source_center_gradient_term;
       candle_q_packed_source_outer_value_term;
       candle_q_packed_source_outer_gradient_term;
       `packed_hessian:(((num#num)#num)#((num#num)#num))list`;
       candle_q_packed_source_center_expr_term;
       candle_q_packed_source_outer_expr_term]
      candle_q_packed_source_object_accept_contract_cell_pass) THEN
  REWRITE_TAC[candle_q_packed_source_object_accept_contract_def] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC
    (ISPECL
      [`center_boxes:(((num#num)#num)#((num#num)#num))list`;
       `outer_boxes:(((num#num)#num)#((num#num)#num))list`;
       `sources:candle_analytic_instruction list`;
       `sources:candle_analytic_instruction list`;
       `center_certificates:(((num#num)#num)#((num#num)#num))list`;
       `outer_certificates:(((num#num)#num)#((num#num)#num))list`;
       candle_q_packed_source_center_item_term;
       candle_q_packed_source_outer_item_term;
       `packed_hessian:(((num#num)#num)#((num#num)#num))list`]
      candle_q_packed_source_certificate_programs_object_invariant) THEN
  ASM_REWRITE_TAC[]);;

(* This lower-level contract retains an explicit source-agreement premise.   *)
(* The closed wrapper below discharges it from shared authenticated replay.  *)

let candle_cv_q_packed_source_certificate_dispatch_entry_accept_contract =
  prove
 (`!source_boxes center_boxes outer_boxes radii codes sources
       center_certificates outer_certificates packed_hessian.
     LENGTH source_boxes = 6 /\
     LENGTH center_boxes = 6 /\
     LENGTH outer_boxes = 6 /\
     candle_q_box_valid_list center_boxes /\
     candle_q_box_valid_list outer_boxes /\
     candle_q_packed_source_correspondence
       source_boxes center_boxes outer_boxes radii /\
     candle_q_packed_source_planned_program_instructions codes sources /\
     (!center_item outer_item.
       candle_q_packed_source_planned_certificate_program_run
         center_boxes codes sources center_certificates []
         (CONS center_item []) [] /\
       candle_q_packed_source_planned_certificate_program_run
         outer_boxes codes sources outer_certificates []
         (CONS outer_item []) []
       ==>
       candle_analytic_erase_sqrt_certificates
         (candle_q_packed_source_item_box_expr center_item) =
       candle_analytic_erase_sqrt_certificates
         (candle_q_packed_source_item_box_expr outer_item)) /\
     candle_cv_q_packed_source_certificate_dispatch_entry
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_packed_source_plan_code_list codes)
       (candle_cv_analytic_instruction_list sources)
       (candle_cv_q_interval_list center_certificates)
       (candle_cv_q_interval_list outer_certificates)
       (candle_cv_q_list radii)
       (candle_cv_q_interval_list packed_hessian) = Cexp_num 1
     ==>
     ?center_item outer_item.
       candle_q_packed_source_certificate_dispatch_accept_contract
         source_boxes center_boxes outer_boxes radii sources
         center_certificates outer_certificates center_item outer_item
         packed_hessian`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
    (ISPECL
      [`candle_cv_q_interval_list center_boxes`;
       `candle_cv_q_interval_list outer_boxes`;
       `candle_cv_q_packed_source_plan_code_list codes`;
       `candle_cv_analytic_instruction_list sources`;
       `candle_cv_q_interval_list center_certificates`;
       `candle_cv_q_interval_list outer_certificates`;
       `candle_cv_q_list radii`;
       `candle_cv_q_interval_list packed_hessian`]
      candle_cv_q_packed_source_certificate_dispatch_entry_components) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
  MP_TAC
    (ISPECL
      [`center_boxes:(((num#num)#num)#((num#num)#num))list`;
       `codes:num list`; `sources:candle_analytic_instruction list`;
       `center_certificates:(((num#num)#num)#((num#num)#num))list`]
      candle_cv_q_packed_source_certificate_dispatch_program_complete_exact) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN
    (X_CHOOSE_THEN candle_q_packed_source_center_item_term
      STRIP_ASSUME_TAC) THEN
  MP_TAC
    (ISPECL
      [`outer_boxes:(((num#num)#num)#((num#num)#num))list`;
       `codes:num list`; `sources:candle_analytic_instruction list`;
       `outer_certificates:(((num#num)#num)#((num#num)#num))list`]
      candle_cv_q_packed_source_certificate_dispatch_program_complete_exact) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN
    (X_CHOOSE_THEN candle_q_packed_source_outer_item_term
      STRIP_ASSUME_TAC) THEN
  EXISTS_TAC candle_q_packed_source_center_item_term THEN
  EXISTS_TAC candle_q_packed_source_outer_item_term THEN
  REWRITE_TAC
    [candle_q_packed_source_certificate_dispatch_accept_contract_def] THEN
  REPEAT CONJ_TAC THEN TRY (ASM_REWRITE_TAC[]) THENL
   [MATCH_MP_TAC
      (ISPECL
        [`center_boxes:(((num#num)#num)#((num#num)#num))list`;
         `codes:num list`; `sources:candle_analytic_instruction list`;
         `center_certificates:(((num#num)#num)#((num#num)#num))list`;
         candle_q_packed_source_empty_stack_term;
         candle_q_packed_source_center_stack_term;
         `[]:(((num#num)#num)#((num#num)#num))list`]
        candle_q_packed_source_planned_certificate_program_run_refines) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC
      (ISPECL
        [`outer_boxes:(((num#num)#num)#((num#num)#num))list`;
         `codes:num list`; `sources:candle_analytic_instruction list`;
         `outer_certificates:(((num#num)#num)#((num#num)#num))list`;
         candle_q_packed_source_empty_stack_term;
         candle_q_packed_source_outer_stack_term;
         `[]:(((num#num)#num)#((num#num)#num))list`]
        candle_q_packed_source_planned_certificate_program_run_refines) THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    (SUBGOAL_THEN `LENGTH (packed_hessian:
        (((num#num)#num)#((num#num)#num))list) = 21` ASSUME_TAC THENL
      [MP_TAC
         (ISPECL
           [mk_conj
              (candle_q_packed_source_center_domain_term,
               candle_q_packed_source_outer_domain_term);
            `radii:((num#num)#num)list`;
            candle_q_packed_source_center_value_term;
            candle_q_packed_source_center_gradient_term;
            `packed_hessian:
               (((num#num)#num)#((num#num)#num))list`]
           candle_cv_q_packed_object_accept6_conditions) THEN
       ANTS_TAC THENL
        [ASSUM_LIST
           (fun assumptions ->
             let lhs_head_name theorem =
               try
                 let left,_ = dest_eq (concl theorem) in
                 let head,_ = strip_comb left in
                 if is_const head then fst (dest_const head) else ""
               with Failure _ -> "" in
             let raw_accept =
               find
                 (fun theorem -> lhs_head_name theorem =
                   "candle_cv_q_packed_object_accept6")
                 assumptions in
             let program_equalities =
               filter
                 (fun theorem -> lhs_head_name theorem =
                   "candle_cv_q_packed_source_certificate_dispatch_program")
                 assumptions in
             let decoded_accept =
               REWRITE_RULE
                 (program_equalities @
                  [candle_cv_q_packed_source_certificate_state_def;
                   candle_q_packed_source_item_results_def; MAP;
                   candle_cv_q_dim_taylor_model_result_list_encode_def;
                   candle_cv_q_interval_list_def; cexp_fst_def; cexp_snd_def;
                   candle_cv_q_dim_taylor_model_result_domain_correct;
                   candle_cv_q_dim_taylor_model_result_value_bound_correct;
                   candle_cv_q_dim_taylor_model_result_gradient_bounds_correct;
                   candle_cv_bool_and_correct])
                 raw_accept in
             ACCEPT_TAC decoded_accept);
         DISCH_THEN
           (fun conditions ->
             let _,rest = CONJ_PAIR conditions in
             let _,rest = CONJ_PAIR rest in
             let _,rest = CONJ_PAIR rest in
             let packed_length,_ = CONJ_PAIR rest in
             ACCEPT_TAC packed_length)];
       ALL_TAC] THEN
     SUBGOAL_THEN
       candle_cv_q_packed_source_dispatch_hessian_encoding_equality_term
       (LABEL_TAC "entry_hessian_encoding") THENL
      [ASSUM_LIST
         (fun assumptions ->
           let lhs_head_name theorem =
             try
               let left,_ = dest_eq (concl theorem) in
               let head,_ = strip_comb left in
               if is_const head then fst (dest_const head) else ""
             with Failure _ -> "" in
           let raw_hessian =
             find
               (fun theorem -> lhs_head_name theorem =
                 "candle_cv_q_packed_hessian6_expand")
               assumptions in
           let program_equalities =
             filter
               (fun theorem -> lhs_head_name theorem =
                 "candle_cv_q_packed_source_certificate_dispatch_program")
               assumptions in
           let decoded_hessian =
             REWRITE_RULE
               (program_equalities @
                [candle_cv_q_packed_source_certificate_state_def;
                 candle_q_packed_source_item_results_def; MAP;
                 candle_cv_q_dim_taylor_model_result_list_encode_def;
                 cexp_fst_def; cexp_snd_def;
                 candle_cv_q_dim_taylor_model_result_hessian_correct])
               raw_hessian in
           ACCEPT_TAC decoded_hessian);
       ALL_TAC] THEN
     let packed_hessian_expand_encoding =
       MATCH_MP candle_cv_q_packed_hessian6_expand_correct
         (ASSUME `LENGTH (packed_hessian:
           (((num#num)#num)#((num#num)#num))list) = 21`) in
     MP_TAC packed_hessian_expand_encoding THEN
     DISCH_THEN
       (fun packed_hessian_expand_encoding ->
         USE_THEN "entry_hessian_encoding"
           (fun entry_hessian_encoding ->
             let encoded_matrix_equality =
               TRANS (SYM packed_hessian_expand_encoding)
                 entry_hessian_encoding in
             let logical_hessian_equality =
               REWRITE_RULE [candle_cv_q_interval_matrix_injective]
                 encoded_matrix_equality in
             ACCEPT_TAC logical_hessian_equality)));
    ASSUM_LIST
      (fun assumptions ->
        let lhs_head_name theorem =
          try
            let left,_ = dest_eq (concl theorem) in
            let head,_ = strip_comb left in
            if is_const head then fst (dest_const head) else ""
          with Failure _ -> "" in
        let raw_accept =
          find
            (fun theorem -> lhs_head_name theorem =
              "candle_cv_q_packed_object_accept6")
            assumptions in
        let program_equalities =
          filter
            (fun theorem -> lhs_head_name theorem =
              "candle_cv_q_packed_source_certificate_dispatch_program")
            assumptions in
        let decoded_accept =
          REWRITE_RULE
            (program_equalities @
             [candle_cv_q_packed_source_certificate_state_def;
              candle_q_packed_source_item_results_def; MAP;
              candle_cv_q_dim_taylor_model_result_list_encode_def;
              candle_cv_q_interval_list_def; cexp_fst_def; cexp_snd_def;
              candle_cv_q_dim_taylor_model_result_domain_correct;
              candle_cv_q_dim_taylor_model_result_value_bound_correct;
              candle_cv_q_dim_taylor_model_result_gradient_bounds_correct;
              candle_cv_bool_and_correct])
            raw_accept in
        ACCEPT_TAC decoded_accept)]);;

let candle_cv_q_packed_source_certificate_dispatch_entry_accept_contract_closed =
  prove
 (`!source_boxes center_boxes outer_boxes radii codes sources
       center_certificates outer_certificates packed_hessian.
     LENGTH source_boxes = 6 /\
     LENGTH center_boxes = 6 /\
     LENGTH outer_boxes = 6 /\
     candle_q_box_valid_list center_boxes /\
     candle_q_box_valid_list outer_boxes /\
     candle_q_packed_source_correspondence
       source_boxes center_boxes outer_boxes radii /\
     candle_q_packed_source_planned_program_instructions codes sources /\
     candle_cv_q_packed_source_certificate_dispatch_entry
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_packed_source_plan_code_list codes)
       (candle_cv_analytic_instruction_list sources)
       (candle_cv_q_interval_list center_certificates)
       (candle_cv_q_interval_list outer_certificates)
       (candle_cv_q_list radii)
       (candle_cv_q_interval_list packed_hessian) = Cexp_num 1
     ==>
     ?center_item outer_item.
       candle_q_packed_source_certificate_dispatch_accept_contract
         source_boxes center_boxes outer_boxes radii sources
         center_certificates outer_certificates center_item outer_item
         packed_hessian`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC
    (ISPECL
      [`source_boxes:(((num#num)#num)#((num#num)#num))list`;
       `center_boxes:(((num#num)#num)#((num#num)#num))list`;
       `outer_boxes:(((num#num)#num)#((num#num)#num))list`;
       `radii:((num#num)#num)list`;
       `codes:num list`; `sources:candle_analytic_instruction list`;
       `center_certificates:(((num#num)#num)#((num#num)#num))list`;
       `outer_certificates:(((num#num)#num)#((num#num)#num))list`;
       `packed_hessian:(((num#num)#num)#((num#num)#num))list`]
      candle_cv_q_packed_source_certificate_dispatch_entry_accept_contract) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_MESON_TAC
    [candle_q_packed_source_planned_certificate_singleton_expr_equal]);;

let candle_cv_q_packed_source_certificate_dispatch_entry_cell_pass = prove
 (`!source_boxes center_boxes outer_boxes radii codes sources
       center_certificates outer_certificates packed_hessian.
     LENGTH source_boxes = 6 /\
     LENGTH center_boxes = 6 /\
     LENGTH outer_boxes = 6 /\
     candle_q_box_valid_list center_boxes /\
     candle_q_box_valid_list outer_boxes /\
     candle_q_packed_source_correspondence
       source_boxes center_boxes outer_boxes radii /\
     candle_q_packed_source_planned_program_instructions codes sources /\
     (!center_item outer_item.
       candle_q_packed_source_planned_certificate_program_run
         center_boxes codes sources center_certificates []
         (CONS center_item []) [] /\
       candle_q_packed_source_planned_certificate_program_run
         outer_boxes codes sources outer_certificates []
         (CONS outer_item []) []
       ==>
       candle_analytic_erase_sqrt_certificates
         (candle_q_packed_source_item_box_expr center_item) =
       candle_analytic_erase_sqrt_certificates
         (candle_q_packed_source_item_box_expr outer_item)) /\
     candle_cv_q_packed_source_certificate_dispatch_entry
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_packed_source_plan_code_list codes)
       (candle_cv_analytic_instruction_list sources)
       (candle_cv_q_interval_list center_certificates)
       (candle_cv_q_interval_list outer_certificates)
       (candle_cv_q_list radii)
       (candle_cv_q_interval_list packed_hessian) = Cexp_num 1
     ==>
     ?expression.
       m_cell_pass (candle_analytic_denote_dim expression)
         ((candle_q_box_lower_vector source_boxes:real^6),
          (candle_q_box_upper_vector source_boxes:real^6))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC
    (MATCH_MP
      (ISPECL
        [`source_boxes:(((num#num)#num)#((num#num)#num))list`;
         `center_boxes:(((num#num)#num)#((num#num)#num))list`;
         `outer_boxes:(((num#num)#num)#((num#num)#num))list`;
         `radii:((num#num)#num)list`;
         `codes:num list`; `sources:candle_analytic_instruction list`;
         `center_certificates:(((num#num)#num)#((num#num)#num))list`;
         `outer_certificates:(((num#num)#num)#((num#num)#num))list`;
         `packed_hessian:(((num#num)#num)#((num#num)#num))list`]
        candle_cv_q_packed_source_certificate_dispatch_entry_accept_contract)
      (ASSUME
        `LENGTH source_boxes = 6 /\
         LENGTH center_boxes = 6 /\ LENGTH outer_boxes = 6 /\
         candle_q_box_valid_list center_boxes /\
         candle_q_box_valid_list outer_boxes /\
         candle_q_packed_source_correspondence
           source_boxes center_boxes outer_boxes radii /\
         candle_q_packed_source_planned_program_instructions codes sources /\
         (!center_item outer_item.
           candle_q_packed_source_planned_certificate_program_run
             center_boxes codes sources center_certificates []
             (CONS center_item []) [] /\
           candle_q_packed_source_planned_certificate_program_run
             outer_boxes codes sources outer_certificates []
             (CONS outer_item []) []
           ==>
           candle_analytic_erase_sqrt_certificates
             (candle_q_packed_source_item_box_expr center_item) =
           candle_analytic_erase_sqrt_certificates
             (candle_q_packed_source_item_box_expr outer_item)) /\
         candle_cv_q_packed_source_certificate_dispatch_entry
           (candle_cv_q_interval_list center_boxes)
           (candle_cv_q_interval_list outer_boxes)
           (candle_cv_q_packed_source_plan_code_list codes)
           (candle_cv_analytic_instruction_list sources)
           (candle_cv_q_interval_list center_certificates)
           (candle_cv_q_interval_list outer_certificates)
           (candle_cv_q_list radii)
           (candle_cv_q_interval_list packed_hessian) = Cexp_num 1`)) THEN
  DISCH_THEN
    (X_CHOOSE_THEN candle_q_packed_source_center_item_term
      (X_CHOOSE_THEN candle_q_packed_source_outer_item_term ASSUME_TAC)) THEN
  EXISTS_TAC candle_q_packed_source_outer_expr_term THEN
  MATCH_MP_TAC
    (ISPECL
      [`source_boxes:(((num#num)#num)#((num#num)#num))list`;
       `center_boxes:(((num#num)#num)#((num#num)#num))list`;
       `outer_boxes:(((num#num)#num)#((num#num)#num))list`;
       `radii:((num#num)#num)list`;
       `sources:candle_analytic_instruction list`;
       `center_certificates:(((num#num)#num)#((num#num)#num))list`;
       `outer_certificates:(((num#num)#num)#((num#num)#num))list`;
       candle_q_packed_source_center_item_term;
       candle_q_packed_source_outer_item_term;
       `packed_hessian:(((num#num)#num)#((num#num)#num))list`]
      candle_q_packed_source_certificate_dispatch_accept_contract_cell_pass) THEN
  ASM_REWRITE_TAC[]);;

let candle_cv_q_packed_source_certificate_dispatch_entry_cell_pass_closed =
  prove
 (`!source_boxes center_boxes outer_boxes radii codes sources
       center_certificates outer_certificates packed_hessian.
     LENGTH source_boxes = 6 /\
     LENGTH center_boxes = 6 /\
     LENGTH outer_boxes = 6 /\
     candle_q_box_valid_list center_boxes /\
     candle_q_box_valid_list outer_boxes /\
     candle_q_packed_source_correspondence
       source_boxes center_boxes outer_boxes radii /\
     candle_q_packed_source_planned_program_instructions codes sources /\
     candle_cv_q_packed_source_certificate_dispatch_entry
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_packed_source_plan_code_list codes)
       (candle_cv_analytic_instruction_list sources)
       (candle_cv_q_interval_list center_certificates)
       (candle_cv_q_interval_list outer_certificates)
       (candle_cv_q_list radii)
       (candle_cv_q_interval_list packed_hessian) = Cexp_num 1
     ==>
     ?expression.
       m_cell_pass (candle_analytic_denote_dim expression)
         ((candle_q_box_lower_vector source_boxes:real^6),
          (candle_q_box_upper_vector source_boxes:real^6))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC
    (ISPECL
      [`source_boxes:(((num#num)#num)#((num#num)#num))list`;
       `center_boxes:(((num#num)#num)#((num#num)#num))list`;
       `outer_boxes:(((num#num)#num)#((num#num)#num))list`;
       `radii:((num#num)#num)list`;
       `codes:num list`; `sources:candle_analytic_instruction list`;
       `center_certificates:(((num#num)#num)#((num#num)#num))list`;
       `outer_certificates:(((num#num)#num)#((num#num)#num))list`;
       `packed_hessian:(((num#num)#num)#((num#num)#num))list`]
      candle_cv_q_packed_source_certificate_dispatch_entry_cell_pass) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_MESON_TAC
    [candle_q_packed_source_planned_certificate_singleton_expr_equal]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_ispair_correct;
     candle_cv_equal_correct;
     candle_cv_q_packed_source_certificate_dispatch_state_complete_correct;
     candle_cv_guarded_accept_one;
     candle_cv_q_packed_source_certificate_dispatch_entry_components;
     candle_q_packed_source_certificate_dispatch_state_complete_shape;
     candle_cv_q_packed_source_certificate_dispatch_program_complete_exact;
     candle_cv_q_interval_list_injective;
     candle_cv_q_interval_matrix_injective;
     candle_q_packed_source_certificate_dispatch_accept_contract_cell_pass;
     candle_cv_q_packed_source_certificate_dispatch_entry_accept_contract;
     candle_cv_q_packed_source_certificate_dispatch_entry_accept_contract_closed;
     candle_cv_q_packed_source_certificate_dispatch_entry_cell_pass;
     candle_cv_q_packed_source_certificate_dispatch_entry_cell_pass_closed] then
  failwith "packed source certificate dispatch entry sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_CERTIFICATE_DISPATCH_ENTRY_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
