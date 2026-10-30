(* ========================================================================== *)
(* Certificate-independent source identity for packed analytic replay.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Center and whole-box executions may use      *)
(* different arithmetic certificates, but a shared authenticated source and  *)
(* plan must construct the same expression after square-root payload erasure. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_certificate_dispatch_program_sound.ml";;

module Candle_cv_analytic_expr_packed_source_identity_sound = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_packed_source_item_invariant;;
open Candle_cv_analytic_expr_packed_source_item_operations_sound;;
open Candle_cv_analytic_expr_packed_source_certified_inverse_sound;;
open Candle_cv_analytic_expr_packed_source_certified_sqrt_sound;;
open Candle_cv_analytic_expr_packed_source_certified_atn_sound;;
open Candle_cv_analytic_expr_packed_source_certificate_program_sound;;
open Candle_cv_analytic_expr_packed_source_certificate_dispatch_compute;;
open Candle_cv_analytic_expr_packed_source_certificate_dispatch_program_sound;;

(* A tiny logical postfix decoder proves that polynomial compilation is      *)
(* injective.  This avoids assuming that two existential polynomial witnesses *)
(* chosen for the same push instruction are syntactically identical.         *)

let candle_poly_decode_head_def = define
 `(candle_poly_decode_head [] = Candle_poly_const 0 0 1) /\
  (candle_poly_decode_head (CONS h t) = h)`;;

let candle_poly_decode_tail_def = define
 `(candle_poly_decode_tail [] = []) /\
  (candle_poly_decode_tail (CONS h t) = t)`;;

let candle_poly_decode_step_def = define
 `(candle_poly_decode_step (Candle_q_push p n d) stack =
     CONS (Candle_poly_const p n d) stack) /\
  (candle_poly_decode_step (Candle_q_load i) stack =
     CONS (Candle_poly_var i) stack) /\
  (candle_poly_decode_step Candle_q_neg stack =
     CONS (Candle_poly_neg (candle_poly_decode_head stack))
       (candle_poly_decode_tail stack)) /\
  (candle_poly_decode_step Candle_q_add stack =
     CONS
       (Candle_poly_add
         (candle_poly_decode_head (candle_poly_decode_tail stack))
         (candle_poly_decode_head stack))
       (candle_poly_decode_tail (candle_poly_decode_tail stack))) /\
  (candle_poly_decode_step Candle_q_mul stack =
     CONS
       (Candle_poly_mul
         (candle_poly_decode_head (candle_poly_decode_tail stack))
         (candle_poly_decode_head stack))
       (candle_poly_decode_tail (candle_poly_decode_tail stack))) /\
  (candle_poly_decode_step Candle_q_square stack =
     CONS (Candle_poly_square (candle_poly_decode_head stack))
       (candle_poly_decode_tail stack))`;;

let candle_poly_decode_run_def = define
 `(candle_poly_decode_run [] stack = stack) /\
  (candle_poly_decode_run (CONS instruction program) stack =
     candle_poly_decode_run program
       (candle_poly_decode_step instruction stack))`;;

let candle_poly_decode_run_append = prove
 (`!left right stack.
     candle_poly_decode_run (APPEND left right) stack =
     candle_poly_decode_run right (candle_poly_decode_run left stack)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; candle_poly_decode_run_def]);;

let candle_poly_decode_compile_run = prove
 (`!polynomial stack.
     candle_poly_decode_run (candle_poly_compile polynomial) stack =
     CONS polynomial stack`,
  MATCH_MP_TAC candle_poly_expr_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC
    [candle_poly_compile_def; candle_poly_decode_run_append;
     candle_poly_decode_run_def; candle_poly_decode_step_def;
     candle_poly_decode_head_def; candle_poly_decode_tail_def;
     APPEND]);;

let candle_poly_compile_injective = prove
 (`!left right.
     candle_poly_compile left = candle_poly_compile right <=> left = right`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN
      (MP_TAC o AP_TERM
        `\program. candle_poly_decode_run program []`) THEN
    REWRITE_TAC[candle_poly_decode_compile_run; CONS_11];
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

let candle_poly_compile_equal = prove
 (`!left right.
     candle_poly_compile left = candle_poly_compile right ==> left = right`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC
    (SPECL [`left:candle_poly_expr`; `right:candle_poly_expr`]
      candle_poly_compile_injective) THEN
  ASM_REWRITE_TAC[]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_poly_decode_run_append;
     candle_poly_decode_compile_run;
     candle_poly_compile_injective;
     candle_poly_compile_equal] then
  failwith "packed source identity: polynomial decoder assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_IDENTITY_POLY_OK DEVELOPMENT_NON_RELEASE";;

let candle_q_packed_source_erased_stack_def = new_definition
 `candle_q_packed_source_erased_stack stack =
    MAP
      (\item. candle_analytic_erase_sqrt_certificates
        (candle_q_packed_source_item_box_expr item)) stack`;;

let candle_q_packed_source_ordinary_step_erased_equal = prove
 (`!left_boxes right_boxes source left_stack right_stack left_next right_next.
     candle_q_packed_source_ordinary_step
       left_boxes source left_stack left_next /\
     candle_q_packed_source_ordinary_step
       right_boxes source right_stack right_next /\
     candle_q_packed_source_erased_stack left_stack =
       candle_q_packed_source_erased_stack right_stack
     ==>
     candle_q_packed_source_erased_stack left_next =
       candle_q_packed_source_erased_stack right_next`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2
      (LABEL_TAC "left_step")
      (CONJUNCTS_THEN2
        (LABEL_TAC "right_step")
        (LABEL_TAC "input_identity"))) THEN
  REMOVE_THEN "left_step" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_source_ordinary_step_def] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  REMOVE_THEN "right_step" MP_TAC THEN
  ASM_REWRITE_TAC
    [candle_q_packed_source_ordinary_step_def;
     distinctness "candle_analytic_instruction";
     injectivity "candle_analytic_instruction"] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  REMOVE_THEN "input_identity" MP_TAC THEN
  ASM_REWRITE_TAC
    [candle_q_packed_source_erased_stack_def;
     candle_q_packed_source_poly_item_def;
     candle_q_packed_source_item_neg_def;
     candle_q_packed_source_item_add_def;
     candle_q_packed_source_item_mul_def;
     candle_q_packed_source_item_square_def;
     candle_q_packed_source_pi_half_item_def;
     candle_q_packed_source_item_make_def;
     candle_q_packed_source_item_box_expr_def;
     candle_analytic_erase_sqrt_certificates_def;
     candle_poly_compile_injective;
     MAP; CONS_11; FST; SND;
     distinctness "candle_analytic_instruction";
     injectivity "candle_analytic_instruction"] THEN
  ASM_MESON_TAC[candle_poly_compile_equal]);;

if hyp candle_q_packed_source_ordinary_step_erased_equal <> [] then
  failwith "packed source identity: ordinary step assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_IDENTITY_ORDINARY_OK DEVELOPMENT_NON_RELEASE";;

let candle_q_packed_source_nonlinear_certificate_step_erased_equal = prove
 (`!left_boxes right_boxes source left_certificates right_certificates
      left_stack right_stack left_next right_next
      left_certificate_rest right_certificate_rest.
     ((source = Candle_analytic_program_inv) \/
      (?source_sqrt.
         source = Candle_analytic_program_sqrt source_sqrt) \/
      (source = Candle_analytic_program_atn)) /\
     candle_q_packed_source_certificate_step
       left_boxes source left_certificates left_stack left_next
       left_certificate_rest /\
     candle_q_packed_source_certificate_step
       right_boxes source right_certificates right_stack right_next
       right_certificate_rest /\
     candle_q_packed_source_erased_stack left_stack =
       candle_q_packed_source_erased_stack right_stack
     ==>
     candle_q_packed_source_erased_stack left_next =
       candle_q_packed_source_erased_stack right_next`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2
      (LABEL_TAC "nonlinear_source")
      (CONJUNCTS_THEN2
        (LABEL_TAC "left_step")
        (CONJUNCTS_THEN2
          (LABEL_TAC "right_step")
          (LABEL_TAC "input_identity")))) THEN
  REMOVE_THEN "nonlinear_source" STRIP_ASSUME_TAC THEN
  REMOVE_THEN "left_step" MP_TAC THEN
  ASM_REWRITE_TAC
    [candle_q_packed_source_certificate_step_def;
     distinctness "candle_analytic_instruction";
     injectivity "candle_analytic_instruction"] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  REMOVE_THEN "right_step" MP_TAC THEN
  ASM_REWRITE_TAC
    [candle_q_packed_source_certificate_step_def;
     distinctness "candle_analytic_instruction";
     injectivity "candle_analytic_instruction"] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  REMOVE_THEN "input_identity" MP_TAC THEN
  ASM_REWRITE_TAC
    [candle_q_packed_source_erased_stack_def;
     candle_q_packed_source_item_inv_certified_def;
     candle_q_packed_source_item_sqrt_certified_def;
     candle_q_packed_source_item_atn_faithful_def;
     candle_q_packed_source_item_make_def;
     candle_q_packed_source_item_box_expr_def;
     candle_packed_analytic_sqrt_with_interval_def;
     candle_analytic_erase_sqrt_certificates_def;
     MAP; CONS_11; FST; SND] THEN
  ASM_MESON_TAC[]);;

if hyp candle_q_packed_source_nonlinear_certificate_step_erased_equal <> [] then
  failwith "packed source identity: nonlinear certificate step assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_IDENTITY_NONLINEAR_OK DEVELOPMENT_NON_RELEASE";;

let candle_q_packed_source_ordinary_certificate_step_erased_equal = prove
 (`!left_boxes right_boxes source left_certificates right_certificates
      left_stack right_stack left_next right_next
      left_certificate_rest right_certificate_rest.
     candle_q_packed_source_ordinary_certificate_step
       left_boxes source left_certificates left_stack left_next
       left_certificate_rest /\
     candle_q_packed_source_ordinary_certificate_step
       right_boxes source right_certificates right_stack right_next
       right_certificate_rest /\
     candle_q_packed_source_erased_stack left_stack =
       candle_q_packed_source_erased_stack right_stack
     ==>
     candle_q_packed_source_erased_stack left_next =
       candle_q_packed_source_erased_stack right_next`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_ordinary_certificate_step_def] THEN
  MESON_TAC
    [candle_q_packed_source_nonlinear_certificate_step_erased_equal;
     candle_q_packed_source_ordinary_step_erased_equal;
     candle_q_packed_source_ordinary_step_not_nonlinear]);;

if hyp candle_q_packed_source_ordinary_certificate_step_erased_equal <> [] then
  failwith "packed source identity: ordinary certificate step assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_IDENTITY_CERTIFICATE_OK DEVELOPMENT_NON_RELEASE";;

let candle_q_packed_source_planned_product_result = prove
 (`!boxes coordinate source certificates stack next certificate_rest.
     coordinate < 3 /\
     candle_q_packed_source_planned_certificate_step
       boxes (SUC coordinate) source certificates stack next certificate_rest
     ==>
     next =
       CONS
         (candle_q_packed_source_item_make
           (candle_q_packed_delta_product_result boxes coordinate)
           (candle_packed_delta_product_source_expr coordinate)
           (candle_packed_delta_product_source_expr coordinate)) stack /\
     certificate_rest = certificates`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_planned_certificate_step_def] THEN
  MESON_TAC
    [NOT_SUC; SUC_INJ;
     ARITH_RULE
       `coordinate < 3 /\
        (coordinate = 3 \/ coordinate = 4 \/ coordinate = 5) ==> F`]);;

let candle_q_packed_source_planned_neg_result = prove
 (`!boxes coordinate source certificates stack next certificate_rest.
     (coordinate = 3 \/ coordinate = 4 \/ coordinate = 5) /\
     candle_q_packed_source_planned_certificate_step
       boxes (SUC coordinate) source certificates stack next certificate_rest
     ==>
     next =
       CONS
         (candle_q_packed_source_item_make
           (candle_q_packed_delta_neg_derivative_result boxes coordinate)
           (candle_packed_delta_neg_derivative_expr coordinate)
           (candle_packed_delta_neg_derivative_expr coordinate)) stack /\
     certificate_rest = certificates`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_planned_certificate_step_def] THEN
  MESON_TAC
    [NOT_SUC; SUC_INJ;
     ARITH_RULE
       `coordinate < 3 /\
        (coordinate = 3 \/ coordinate = 4 \/ coordinate = 5) ==> F`]);;

let candle_q_packed_source_planned_certificate_step_erased_equal = prove
 (`!left_boxes right_boxes code source
      left_certificates right_certificates left_stack right_stack
      left_next right_next left_certificate_rest right_certificate_rest.
     candle_q_packed_source_planned_certificate_step
       left_boxes code source left_certificates left_stack left_next
       left_certificate_rest /\
     candle_q_packed_source_planned_certificate_step
       right_boxes code source right_certificates right_stack right_next
       right_certificate_rest /\
     candle_q_packed_source_erased_stack left_stack =
       candle_q_packed_source_erased_stack right_stack
     ==>
     candle_q_packed_source_erased_stack left_next =
       candle_q_packed_source_erased_stack right_next`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2
      (LABEL_TAC "left_step")
      (CONJUNCTS_THEN2
        (LABEL_TAC "right_step")
        (LABEL_TAC "input_identity"))) THEN
  REMOVE_THEN "left_step" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_source_planned_certificate_step_def] THEN
  DISCH_THEN STRIP_ASSUME_TAC THENL
   [REMOVE_THEN "right_step" MP_TAC THEN
    ASM_REWRITE_TAC
      [candle_q_packed_source_planned_certificate_step_def; NOT_SUC] THEN
    DISCH_TAC THEN
    ASM_MESON_TAC
      [candle_q_packed_source_ordinary_certificate_step_erased_equal];
    REMOVE_THEN "right_step"
      (fun right_step ->
        MP_TAC
          (MATCH_MP
            (SPEC_ALL candle_q_packed_source_planned_product_result)
            (CONJ (ASSUME `coordinate < 3`)
              (SUBS [ASSUME `code = SUC coordinate`] right_step)))) THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN
    REMOVE_THEN "input_identity" MP_TAC THEN
    ASM_REWRITE_TAC
      [candle_q_packed_source_erased_stack_def;
       candle_q_packed_source_item_make_def;
       candle_q_packed_source_item_box_expr_def;
       MAP; CONS_11; FST; SND];
    SUBGOAL_THEN
      `coordinate = 3 \/ coordinate = 4 \/ coordinate = 5`
      (LABEL_TAC "neg_coordinate") THENL
     [ASM_REWRITE_TAC[];
      REMOVE_THEN "right_step"
        (fun right_step ->
          MP_TAC
            (MATCH_MP
              (SPEC_ALL candle_q_packed_source_planned_neg_result)
              (CONJ
                (ASSUME
                  `coordinate = 3 \/ coordinate = 4 \/ coordinate = 5`)
                (SUBS [ASSUME `code = SUC coordinate`] right_step)))) THEN
      DISCH_THEN STRIP_ASSUME_TAC THEN
      REMOVE_THEN "input_identity" MP_TAC THEN
      ASM_REWRITE_TAC
        [candle_q_packed_source_erased_stack_def;
         candle_q_packed_source_item_make_def;
         candle_q_packed_source_item_box_expr_def;
         MAP; CONS_11; FST; SND]];
    SUBGOAL_THEN
      `coordinate = 3 \/ coordinate = 4 \/ coordinate = 5`
      (LABEL_TAC "neg_coordinate") THENL
     [ASM_REWRITE_TAC[];
      REMOVE_THEN "right_step"
        (fun right_step ->
          MP_TAC
            (MATCH_MP
              (SPEC_ALL candle_q_packed_source_planned_neg_result)
              (CONJ
                (ASSUME
                  `coordinate = 3 \/ coordinate = 4 \/ coordinate = 5`)
                (SUBS [ASSUME `code = SUC coordinate`] right_step)))) THEN
      DISCH_THEN STRIP_ASSUME_TAC THEN
      REMOVE_THEN "input_identity" MP_TAC THEN
      ASM_REWRITE_TAC
        [candle_q_packed_source_erased_stack_def;
         candle_q_packed_source_item_make_def;
         candle_q_packed_source_item_box_expr_def;
         MAP; CONS_11; FST; SND]];
    SUBGOAL_THEN
      `coordinate = 3 \/ coordinate = 4 \/ coordinate = 5`
      (LABEL_TAC "neg_coordinate") THENL
     [ASM_REWRITE_TAC[];
      REMOVE_THEN "right_step"
        (fun right_step ->
          MP_TAC
            (MATCH_MP
              (SPEC_ALL candle_q_packed_source_planned_neg_result)
              (CONJ
                (ASSUME
                  `coordinate = 3 \/ coordinate = 4 \/ coordinate = 5`)
                (SUBS [ASSUME `code = SUC coordinate`] right_step)))) THEN
      DISCH_THEN STRIP_ASSUME_TAC THEN
      REMOVE_THEN "input_identity" MP_TAC THEN
      ASM_REWRITE_TAC
        [candle_q_packed_source_erased_stack_def;
         candle_q_packed_source_item_make_def;
         candle_q_packed_source_item_box_expr_def;
         MAP; CONS_11; FST; SND]]]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_source_planned_product_result;
     candle_q_packed_source_planned_neg_result;
     candle_q_packed_source_planned_certificate_step_erased_equal] then
  failwith "packed source identity: planned certificate step assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_IDENTITY_PLANNED_OK DEVELOPMENT_NON_RELEASE";;

let candle_q_packed_source_planned_certificate_program_erased_equal = prove
 (`!codes sources left_boxes right_boxes
      left_certificates right_certificates left_stack right_stack
      left_result right_result left_certificate_rest right_certificate_rest.
     candle_q_packed_source_planned_certificate_program_run
       left_boxes codes sources left_certificates left_stack left_result
       left_certificate_rest /\
     candle_q_packed_source_planned_certificate_program_run
       right_boxes codes sources right_certificates right_stack right_result
       right_certificate_rest /\
     candle_q_packed_source_erased_stack left_stack =
       candle_q_packed_source_erased_stack right_stack
     ==>
     candle_q_packed_source_erased_stack left_result =
       candle_q_packed_source_erased_stack right_result`,
  LIST_INDUCT_TAC THENL
   [GEN_TAC THEN
    MP_TAC (ISPEC `sources:candle_analytic_instruction list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_q_packed_source_planned_certificate_program_run_def] THEN
    MESON_TAC[];
    POP_ASSUM (LABEL_TAC "induction_hypothesis") THEN
    GEN_TAC THEN
    MP_TAC (ISPEC `sources:candle_analytic_instruction list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THENL
     [REPEAT GEN_TAC THEN
      REWRITE_TAC
        [candle_q_packed_source_planned_certificate_program_run_def];
      REPEAT GEN_TAC THEN
      REWRITE_TAC
        [candle_q_packed_source_planned_certificate_program_run_def] THEN
      DISCH_THEN
        (CONJUNCTS_THEN2
          (REPEAT_TCL CHOOSE_THEN
            (CONJUNCTS_THEN2
              (LABEL_TAC "left_head")
              (LABEL_TAC "left_tail")))
          (CONJUNCTS_THEN2
            (REPEAT_TCL CHOOSE_THEN
              (CONJUNCTS_THEN2
                (LABEL_TAC "right_head")
                (LABEL_TAC "right_tail")))
            (LABEL_TAC "input_identity"))) THEN
      REMOVE_THEN "left_head"
        (fun left_head ->
          REMOVE_THEN "right_head"
            (fun right_head ->
              USE_THEN "input_identity"
                (fun input_identity ->
                  MP_TAC
                    (MATCH_MP
                      (SPEC_ALL
                        candle_q_packed_source_planned_certificate_step_erased_equal)
                      (CONJ left_head
                        (CONJ right_head input_identity)))))) THEN
      DISCH_THEN (LABEL_TAC "next_identity") THEN
      REMOVE_THEN "left_tail"
        (fun left_tail ->
          REMOVE_THEN "right_tail"
            (fun right_tail ->
              USE_THEN "next_identity"
                (fun next_identity ->
                  USE_THEN "induction_hypothesis"
                    (fun induction_hypothesis ->
                      MATCH_ACCEPT_TAC
                        (MATCH_MP (SPEC_ALL induction_hypothesis)
                          (CONJ left_tail
                            (CONJ right_tail next_identity)))))))]]);;

if hyp candle_q_packed_source_planned_certificate_program_erased_equal <> [] then
  failwith "packed source identity: planned program assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_IDENTITY_PROGRAM_INDUCTION_OK DEVELOPMENT_NON_RELEASE";;

let candle_q_packed_source_planned_certificate_singleton_expr_equal = prove
 (`!codes sources left_boxes right_boxes
      left_certificates right_certificates left_item right_item
      left_certificate_rest right_certificate_rest.
     candle_q_packed_source_planned_certificate_program_run
       left_boxes codes sources left_certificates [] [left_item]
       left_certificate_rest /\
     candle_q_packed_source_planned_certificate_program_run
       right_boxes codes sources right_certificates [] [right_item]
       right_certificate_rest
     ==>
     candle_analytic_erase_sqrt_certificates
       (candle_q_packed_source_item_box_expr left_item) =
     candle_analytic_erase_sqrt_certificates
       (candle_q_packed_source_item_box_expr right_item)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "left_run") (LABEL_TAC "right_run")) THEN
  REMOVE_THEN "left_run"
    (fun left_run ->
      REMOVE_THEN "right_run"
        (fun right_run ->
          let rule =
            SPEC_ALL
              candle_q_packed_source_planned_certificate_program_erased_equal in
          let antecedent,_ = dest_imp (concl rule) in
          let _,right_and_identity = dest_conj antecedent in
          let _,input_identity_pattern = dest_conj right_and_identity in
          let erased_left,_ = dest_eq input_identity_pattern in
          let erased_function = rator erased_left in
          let _,left_run_arguments = strip_comb (concl left_run) in
          let left_stack = el 4 left_run_arguments in
          let input_identity =
            REFL (mk_comb (erased_function,left_stack)) in
          MP_TAC
            (MATCH_MP rule
              (CONJ left_run (CONJ right_run input_identity))))) THEN
  REWRITE_TAC
    [candle_q_packed_source_erased_stack_def; MAP; CONS_11]);;

if hyp candle_q_packed_source_planned_certificate_singleton_expr_equal <> [] then
  failwith "packed source identity: singleton expression assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_IDENTITY_PROGRAM_OK DEVELOPMENT_NON_RELEASE";;

end;;
