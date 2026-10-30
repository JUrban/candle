(* ========================================================================== *)
(* Planned executable dispatch for certificate-driven packed source replay.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Code zero selects the ordinary source step.   *)
(* Codes 1--6 select, respectively, the six authenticated delta source       *)
(* specializations at coordinates 0--5.  The explicit code records the same  *)
(* choice made by the checked source-to-prepared compiler: it prevents the    *)
(* executable path from silently replacing a tight specialized result by the *)
(* also-sound but generally looser polynomial interpretation.                 *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_certificate_step_compute.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_delta_product_result_compute.ml";;

module Candle_cv_analytic_expr_packed_source_certificate_dispatch_compute = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_analytic_expr_taylor_model_program_compute;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_packed_source_item_invariant;;
open Candle_cv_analytic_expr_packed_source_item_operations_sound;;
open Candle_cv_analytic_expr_packed_source_delta_specialization_sound;;
open Candle_cv_analytic_expr_packed_source_step_sound;;
open Candle_cv_analytic_expr_packed_source_certificate_program_sound;;
open Candle_cv_analytic_expr_packed_source_certificate_step_compute;;
open Candle_cv_analytic_expr_packed_source_delta_neg_derivative_result_compute;;
open Candle_cv_analytic_expr_packed_source_delta_product_result_compute;;

(* The ordinary relation deliberately excludes the optimized delta branch.   *)
(* A recognized delta source is still accepted at code zero through its      *)
(* generic polynomial interpretation; codes one through six select the tight *)
(* specialized result.  Thus the plan, rather than relational nondeterminism, *)
(* determines the exact successor state.                                     *)

let candle_q_packed_source_ordinary_step_def = new_definition
 `candle_q_packed_source_ordinary_step boxes source stack next <=>
    (?polynomial.
       candle_poly_valid_dim 6 polynomial /\
       source =
         Candle_analytic_push_poly (candle_poly_compile polynomial) /\
       next =
         CONS (candle_q_packed_source_poly_item boxes polynomial) stack) \/
    (?item rest.
       source = Candle_analytic_program_neg /\
       stack = CONS item rest /\
       next = CONS (candle_q_packed_source_item_neg boxes item) rest) \/
    (?right left rest.
       source = Candle_analytic_program_add /\
       stack = CONS right (CONS left rest) /\
       next =
         CONS (candle_q_packed_source_item_add boxes left right) rest) \/
    (?right left rest.
       source = Candle_analytic_program_mul /\
       stack = CONS right (CONS left rest) /\
       next =
         CONS (candle_q_packed_source_item_mul boxes left right) rest) \/
    (?item rest.
       source = Candle_analytic_program_square /\
       stack = CONS item rest /\
       next = CONS (candle_q_packed_source_item_square boxes item) rest) \/
    (source = Candle_analytic_program_pi_half /\
     next = CONS (candle_q_packed_source_pi_half_item boxes) stack)`;;

let candle_q_packed_source_ordinary_step_source_step = prove
 (`!boxes source stack next.
     candle_q_packed_source_ordinary_step boxes source stack next
     ==> candle_q_packed_source_step boxes source stack next`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_ordinary_step_def] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  REWRITE_TAC[candle_q_packed_source_step_def] THENL
   [DISJ1_TAC THEN ASM_MESON_TAC[];
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN ASM_MESON_TAC[];
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
    ASM_MESON_TAC[];
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
    DISJ1_TAC THEN ASM_MESON_TAC[];
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
    DISJ2_TAC THEN DISJ1_TAC THEN ASM_MESON_TAC[];
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
    DISJ2_TAC THEN ASM_REWRITE_TAC[]]);;

let _ = print_endline "CANDLE_CERT_DISPATCH_STAGE ordinary-source";;

let candle_q_packed_source_ordinary_step_not_nonlinear = prove
 (`!boxes source stack next.
     candle_q_packed_source_ordinary_step boxes source stack next
     ==>
     ~(source = Candle_analytic_program_inv) /\
     (!source_sqrt. ~(source = Candle_analytic_program_sqrt source_sqrt)) /\
     ~(source = Candle_analytic_program_atn)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_ordinary_step_def] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  ASM_REWRITE_TAC[distinctness "candle_analytic_instruction"]);;

let _ = print_endline "CANDLE_CERT_DISPATCH_STAGE ordinary-distinct";;

let candle_q_packed_source_ordinary_certificate_step_def = new_definition
 `candle_q_packed_source_ordinary_certificate_step
      boxes source certificates stack next certificate_rest <=>
    (((source = Candle_analytic_program_inv) \/
      (?source_sqrt. source = Candle_analytic_program_sqrt source_sqrt) \/
      (source = Candle_analytic_program_atn)) /\
     candle_q_packed_source_certificate_step
       boxes source certificates stack next certificate_rest) \/
    (candle_q_packed_source_ordinary_step boxes source stack next /\
     certificate_rest = certificates)`;;

let candle_q_packed_source_ordinary_step_certificate_step = prove
 (`!boxes source certificates stack next.
     candle_q_packed_source_ordinary_step boxes source stack next
     ==>
     candle_q_packed_source_certificate_step
       boxes source certificates stack next certificates`,
  REPEAT GEN_TAC THEN DISCH_THEN (LABEL_TAC "ordinary") THEN
  USE_THEN "ordinary"
    (fun theorem ->
      MP_TAC (MATCH_MP
        (SPEC_ALL candle_q_packed_source_ordinary_step_not_nonlinear)
        theorem)) THEN
  USE_THEN "ordinary"
    (fun theorem ->
      MP_TAC (MATCH_MP
        (SPEC_ALL candle_q_packed_source_ordinary_step_source_step)
        theorem)) THEN
  REWRITE_TAC[candle_q_packed_source_certificate_step_def] THEN
  MESON_TAC[]);;

let candle_q_packed_source_ordinary_certificate_step_certificate_step = prove
 (`!boxes source certificates stack next certificate_rest.
     candle_q_packed_source_ordinary_certificate_step
       boxes source certificates stack next certificate_rest
     ==>
     candle_q_packed_source_certificate_step
       boxes source certificates stack next certificate_rest`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_ordinary_certificate_step_def] THEN
  MESON_TAC[candle_q_packed_source_ordinary_step_certificate_step]);;

let _ = print_endline "CANDLE_CERT_DISPATCH_STAGE ordinary-certificate";;

(* The logical planned step is deterministic about the optimized/non-       *)
(* optimized choice while retaining the established certificate semantics.  *)

let candle_q_packed_source_planned_certificate_step_def = new_definition
 `candle_q_packed_source_planned_certificate_step
      boxes code source certificates stack next certificate_rest <=>
    (code = 0 /\
     candle_q_packed_source_ordinary_certificate_step
       boxes source certificates stack next certificate_rest) \/
    (?coordinate.
       code = SUC coordinate /\
       coordinate < 3 /\
       candle_packed_delta_product_source_instruction coordinate source /\
       next =
         CONS
           (candle_q_packed_source_item_make
             (candle_q_packed_delta_product_result boxes coordinate)
             (candle_packed_delta_product_source_expr coordinate)
             (candle_packed_delta_product_source_expr coordinate)) stack /\
       certificate_rest = certificates) \/
    (?coordinate.
       code = SUC coordinate /\
       (coordinate = 3 \/ coordinate = 4 \/ coordinate = 5) /\
       candle_packed_delta_neg_derivative_source_instruction coordinate source /\
       next =
         CONS
           (candle_q_packed_source_item_make
             (candle_q_packed_delta_neg_derivative_result boxes coordinate)
             (candle_packed_delta_neg_derivative_expr coordinate)
             (candle_packed_delta_neg_derivative_expr coordinate)) stack /\
       certificate_rest = certificates)`;;

let candle_q_packed_delta_product_planned_source_step = prove
 (`!boxes coordinate source stack.
     candle_packed_delta_product_source_instruction coordinate source
     ==>
     candle_q_packed_source_step boxes source stack
       (CONS
         (candle_q_packed_source_item_make
           (candle_q_packed_delta_product_result boxes coordinate)
           (candle_packed_delta_product_source_expr coordinate)
           (candle_packed_delta_product_source_expr coordinate)) stack)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_q_packed_source_step_def] THEN
  DISJ2_TAC THEN DISJ1_TAC THEN
  EXISTS_TAC `candle_q_packed_delta_product_result boxes coordinate` THEN
  EXISTS_TAC `candle_packed_delta_product_source_expr coordinate` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_q_packed_delta_specialized_source_result_def] THEN
    DISJ2_TAC THEN EXISTS_TAC `coordinate:num` THEN ASM_REWRITE_TAC[];
    REFL_TAC]);;

let _ = print_endline "CANDLE_CERT_DISPATCH_STAGE product-source";;

let candle_q_packed_delta_neg_derivative_planned_source_step = prove
 (`!boxes coordinate source stack.
     candle_packed_delta_neg_derivative_source_instruction coordinate source
     ==>
     candle_q_packed_source_step boxes source stack
       (CONS
         (candle_q_packed_source_item_make
           (candle_q_packed_delta_neg_derivative_result boxes coordinate)
           (candle_packed_delta_neg_derivative_expr coordinate)
           (candle_packed_delta_neg_derivative_expr coordinate)) stack)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_q_packed_source_step_def] THEN
  DISJ2_TAC THEN DISJ1_TAC THEN
  EXISTS_TAC
    `candle_q_packed_delta_neg_derivative_result boxes coordinate` THEN
  EXISTS_TAC `candle_packed_delta_neg_derivative_expr coordinate` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_q_packed_delta_specialized_source_result_def] THEN
    DISJ1_TAC THEN EXISTS_TAC `coordinate:num` THEN ASM_REWRITE_TAC[];
    REFL_TAC]);;

let _ = print_endline "CANDLE_CERT_DISPATCH_STAGE neg-source";;

let candle_q_packed_delta_product_planned_certificate_step = prove
 (`!boxes coordinate source certificates stack.
     candle_packed_delta_product_source_instruction coordinate source
     ==>
     candle_q_packed_source_certificate_step
       boxes source certificates stack
       (CONS
         (candle_q_packed_source_item_make
           (candle_q_packed_delta_product_result boxes coordinate)
           (candle_packed_delta_product_source_expr coordinate)
           (candle_packed_delta_product_source_expr coordinate)) stack)
       certificates`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_q_packed_source_certificate_step_def] THEN
  DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_packed_delta_product_source_instruction_def]) THEN
  ASM_REWRITE_TAC[distinctness "candle_analytic_instruction"] THEN
  MATCH_MP_TAC candle_q_packed_delta_product_planned_source_step THEN
  ASM_REWRITE_TAC[candle_packed_delta_product_source_instruction_def]);;

let candle_q_packed_delta_neg_derivative_planned_certificate_step = prove
 (`!boxes coordinate source certificates stack.
     candle_packed_delta_neg_derivative_source_instruction coordinate source
     ==>
     candle_q_packed_source_certificate_step
       boxes source certificates stack
       (CONS
         (candle_q_packed_source_item_make
           (candle_q_packed_delta_neg_derivative_result boxes coordinate)
           (candle_packed_delta_neg_derivative_expr coordinate)
           (candle_packed_delta_neg_derivative_expr coordinate)) stack)
       certificates`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_q_packed_source_certificate_step_def] THEN
  DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE
      [candle_packed_delta_neg_derivative_source_instruction_def]) THEN
  ASM_REWRITE_TAC[distinctness "candle_analytic_instruction"] THEN
  MATCH_MP_TAC candle_q_packed_delta_neg_derivative_planned_source_step THEN
  ASM_REWRITE_TAC
    [candle_packed_delta_neg_derivative_source_instruction_def]);;

let _ = print_endline "CANDLE_CERT_DISPATCH_STAGE specialized-certificate";;

let candle_q_packed_source_planned_certificate_step_source_step = prove
 (`!boxes code source certificates stack next certificate_rest.
     candle_q_packed_source_planned_certificate_step
       boxes code source certificates stack next certificate_rest
     ==>
     candle_q_packed_source_certificate_step
       boxes source certificates stack next certificate_rest`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_planned_certificate_step_def] THEN
  MESON_TAC
   [candle_q_packed_source_ordinary_certificate_step_certificate_step;
    candle_q_packed_delta_product_planned_certificate_step;
    candle_q_packed_delta_neg_derivative_planned_certificate_step]);;

let _ = print_endline "CANDLE_CERT_DISPATCH_STAGE planned-step";;

(* Result-stack projection lemmas used by the executable refinement. *)

let candle_q_packed_source_item_results_poly = prove
 (`!boxes polynomial rest.
     candle_q_packed_source_item_results
       (CONS (candle_q_packed_source_poly_item boxes polynomial) rest) =
     CONS
       (candle_q_dim_taylor_model_poly_program
         (candle_q_center_environment_list boxes) boxes
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_poly_compile polynomial))
       (candle_q_packed_source_item_results rest)`,
  REWRITE_TAC
    [candle_q_packed_source_item_results_def; MAP;
     candle_q_packed_source_poly_item_def;
     candle_q_packed_source_item_make_def;
     candle_q_packed_source_item_result_def; FST; SND]);;

let candle_q_packed_source_item_results_neg = prove
 (`!boxes item rest.
     candle_q_packed_source_item_results
       (CONS (candle_q_packed_source_item_neg boxes item) rest) =
     CONS
       (candle_q_dim_taylor_model_result_neg
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_q_packed_source_item_result item))
       (candle_q_packed_source_item_results rest)`,
  REWRITE_TAC
    [candle_q_packed_source_item_results_def; MAP;
     candle_q_packed_source_item_neg_def;
     candle_q_packed_source_item_make_def;
     candle_q_packed_source_item_result_def; FST; SND]);;

let candle_q_packed_source_item_results_add = prove
 (`!boxes left right rest.
     candle_q_packed_source_item_results
       (CONS (candle_q_packed_source_item_add boxes left right) rest) =
     CONS
       (candle_q_dim_taylor_model_result_add
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_q_packed_source_item_result left)
         (candle_q_packed_source_item_result right))
       (candle_q_packed_source_item_results rest)`,
  REWRITE_TAC
    [candle_q_packed_source_item_results_def; MAP;
     candle_q_packed_source_item_add_def;
     candle_q_packed_source_item_make_def;
     candle_q_packed_source_item_result_def; FST; SND]);;

let candle_q_packed_source_item_results_mul = prove
 (`!boxes left right rest.
     candle_q_packed_source_item_results
       (CONS (candle_q_packed_source_item_mul boxes left right) rest) =
     CONS
       (candle_q_dim_taylor_model_result_mul
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_q_packed_source_item_result left)
         (candle_q_packed_source_item_result right))
       (candle_q_packed_source_item_results rest)`,
  REWRITE_TAC
    [candle_q_packed_source_item_results_def; MAP;
     candle_q_packed_source_item_mul_def;
     candle_q_packed_source_item_make_def;
     candle_q_packed_source_item_result_def; FST; SND]);;

let candle_q_packed_source_item_results_square = prove
 (`!boxes item rest.
     candle_q_packed_source_item_results
       (CONS (candle_q_packed_source_item_square boxes item) rest) =
     CONS
       (candle_q_dim_taylor_model_result_square
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_q_packed_source_item_result item))
       (candle_q_packed_source_item_results rest)`,
  REWRITE_TAC
    [candle_q_packed_source_item_results_def; MAP;
     candle_q_packed_source_item_square_def;
     candle_q_packed_source_item_make_def;
     candle_q_packed_source_item_result_def; FST; SND]);;

let candle_q_packed_source_item_results_pi_half = prove
 (`!boxes rest.
     candle_q_packed_source_item_results
       (CONS (candle_q_packed_source_pi_half_item boxes) rest) =
     CONS
       (candle_q_dim_taylor_model_result_pi_half
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_q_center_environment_list boxes) boxes)
       (candle_q_packed_source_item_results rest)`,
  REWRITE_TAC
    [candle_q_packed_source_item_results_def; MAP;
     candle_q_packed_source_pi_half_item_def;
     candle_q_packed_source_item_make_def;
     candle_q_packed_source_item_result_def; FST; SND]);;

let candle_q_packed_source_item_results_make = prove
 (`!result center_e box_e rest.
     candle_q_packed_source_item_results
       (CONS (candle_q_packed_source_item_make result center_e box_e) rest) =
     CONS result (candle_q_packed_source_item_results rest)`,
  REWRITE_TAC
    [candle_q_packed_source_item_results_def; MAP;
     candle_q_packed_source_item_make_def;
     candle_q_packed_source_item_result_def; FST; SND]);;

(* Transactional ordinary dispatch.  Any malformed instruction or stack     *)
(* returns the original stack/certificate stream with a false status.        *)

let candle_cv_q_packed_source_certificate_ordinary_step_def = new_definition
 `candle_cv_q_packed_source_certificate_ordinary_step
      boxes source certificates stack =
    let radii =
      candle_cv_q_fixed_list_round_upper (candle_cv_q_radius_list boxes) in
    Cexp_if (Cexp_ispair source)
      (Cexp_if (Cexp_eq (Cexp_fst source) (Cexp_num 0))
        (candle_cv_q_packed_source_certificate_state T
          (Cexp_pair
            (candle_cv_q_dim_taylor_model_poly_program
              (candle_cv_q_center_environment_list boxes) boxes radii
              (Cexp_snd source)) stack)
          certificates)
        (Cexp_if (Cexp_eq (Cexp_fst source) (Cexp_num 1))
          (candle_cv_q_packed_source_certificate_sqrt_step
            boxes certificates stack)
          (candle_cv_q_packed_source_certificate_failure stack certificates)))
      (Cexp_if (Cexp_eq source (Cexp_num 2))
        (Cexp_if (Cexp_ispair stack)
          (candle_cv_q_packed_source_certificate_state T
            (Cexp_pair
              (candle_cv_q_dim_taylor_model_result_neg radii
                (Cexp_fst stack))
              (Cexp_snd stack))
            certificates)
          (candle_cv_q_packed_source_certificate_failure stack certificates))
        (Cexp_if (Cexp_eq source (Cexp_num 3))
          (Cexp_if (Cexp_ispair stack)
            (Cexp_if (Cexp_ispair (Cexp_snd stack))
              (candle_cv_q_packed_source_certificate_state T
                (Cexp_pair
                  (candle_cv_q_dim_taylor_model_result_add radii
                    (Cexp_fst (Cexp_snd stack)) (Cexp_fst stack))
                  (Cexp_snd (Cexp_snd stack)))
                certificates)
              (candle_cv_q_packed_source_certificate_failure
                stack certificates))
            (candle_cv_q_packed_source_certificate_failure stack certificates))
          (Cexp_if (Cexp_eq source (Cexp_num 4))
            (Cexp_if (Cexp_ispair stack)
              (Cexp_if (Cexp_ispair (Cexp_snd stack))
                (candle_cv_q_packed_source_certificate_state T
                  (Cexp_pair
                    (candle_cv_q_dim_taylor_model_result_mul radii
                      (Cexp_fst (Cexp_snd stack)) (Cexp_fst stack))
                    (Cexp_snd (Cexp_snd stack)))
                  certificates)
                (candle_cv_q_packed_source_certificate_failure
                  stack certificates))
              (candle_cv_q_packed_source_certificate_failure
                stack certificates))
            (Cexp_if (Cexp_eq source (Cexp_num 5))
              (Cexp_if (Cexp_ispair stack)
                (candle_cv_q_packed_source_certificate_state T
                  (Cexp_pair
                    (candle_cv_q_dim_taylor_model_result_square radii
                      (Cexp_fst stack))
                    (Cexp_snd stack))
                  certificates)
                (candle_cv_q_packed_source_certificate_failure
                  stack certificates))
              (Cexp_if (Cexp_eq source (Cexp_num 6))
                (candle_cv_q_packed_source_certificate_inv_step
                  boxes certificates stack)
                (Cexp_if (Cexp_eq source (Cexp_num 7))
                  (candle_cv_q_packed_source_certificate_atn_step
                    boxes certificates stack)
                  (Cexp_if (Cexp_eq source (Cexp_num 8))
                    (candle_cv_q_packed_source_certificate_state T
                      (Cexp_pair
                        (candle_cv_q_dim_taylor_model_result_pi_half radii
                          (candle_cv_q_center_environment_list boxes) boxes)
                        stack)
                      certificates)
                    (candle_cv_q_packed_source_certificate_failure
                      stack certificates))))))))`;;

let candle_cv_q_packed_source_certificate_ordinary_algebraic_correct = prove
 (`!boxes source certificates stack next.
     candle_q_packed_source_ordinary_step boxes source stack next
     ==>
     candle_cv_q_packed_source_certificate_ordinary_step
       (candle_cv_q_interval_list boxes)
       (candle_cv_analytic_instruction source)
       (candle_cv_q_interval_list certificates)
       (candle_cv_q_dim_taylor_model_result_list_encode
         (candle_q_packed_source_item_results stack)) =
     candle_cv_q_packed_source_certificate_state T
       (candle_cv_q_dim_taylor_model_result_list_encode
         (candle_q_packed_source_item_results next))
       (candle_cv_q_interval_list certificates)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_ordinary_step_def] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  ASM_REWRITE_TAC
   [candle_cv_q_packed_source_certificate_ordinary_step_def;
    LET_DEF; LET_END_DEF; candle_cv_analytic_instruction_def;
    candle_q_packed_source_item_results_poly;
    candle_q_packed_source_item_results_neg;
    candle_q_packed_source_item_results_add;
    candle_q_packed_source_item_results_mul;
    candle_q_packed_source_item_results_square;
    candle_q_packed_source_item_results_pi_half;
    candle_cv_q_radius_list_correct;
    candle_cv_q_center_environment_list_correct;
    candle_cv_q_fixed_list_round_upper_correct] THEN
  REWRITE_TAC
   [candle_q_packed_source_item_results_cons;
    candle_cv_q_dim_taylor_model_result_list_encode_def;
    cexp_ispair_def; cexp_fst_def; cexp_snd_def; cexp_eq_def; cexp_if_def;
    injectivity "cval"; distinctness "cval"; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC
   [cexp_if_def;
    candle_cv_q_dim_taylor_model_poly_program_correct;
    candle_cv_q_dim_taylor_model_result_neg_correct;
    candle_cv_q_dim_taylor_model_result_add_correct;
    candle_cv_q_dim_taylor_model_result_mul_correct;
    candle_cv_q_dim_taylor_model_result_square_correct;
    candle_cv_q_dim_taylor_model_result_pi_half_correct]);;

let candle_cv_q_packed_source_certificate_ordinary_inv_correct = prove
 (`!boxes certificates stack next certificate_rest.
    candle_q_packed_source_certificate_step boxes
      Candle_analytic_program_inv certificates stack next certificate_rest
    ==>
    candle_cv_q_packed_source_certificate_ordinary_step
      (candle_cv_q_interval_list boxes)
      (candle_cv_analytic_instruction Candle_analytic_program_inv)
      (candle_cv_q_interval_list certificates)
      (candle_cv_q_dim_taylor_model_result_list_encode
        (candle_q_packed_source_item_results stack)) =
    candle_cv_q_packed_source_certificate_state T
      (candle_cv_q_dim_taylor_model_result_list_encode
        (candle_q_packed_source_item_results next))
      (candle_cv_q_interval_list certificate_rest)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC
   [candle_cv_q_packed_source_certificate_ordinary_step_def;
    LET_DEF; LET_END_DEF; candle_cv_analytic_instruction_def;
    cexp_ispair_def; cexp_eq_def; cexp_if_def;
    injectivity "cval"; distinctness "cval"; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[cexp_if_def] THEN
  MATCH_MP_TAC candle_cv_q_packed_source_certificate_inv_step_refines THEN
  ASM_REWRITE_TAC[]);;

let candle_cv_q_packed_source_certificate_ordinary_sqrt_select = prove
 (`!boxes source_sqrt certificates stack.
    candle_cv_q_packed_source_certificate_ordinary_step
      (candle_cv_q_interval_list boxes)
      (candle_cv_analytic_instruction
        (Candle_analytic_program_sqrt source_sqrt))
      (candle_cv_q_interval_list certificates) stack =
    candle_cv_q_packed_source_certificate_sqrt_step
      (candle_cv_q_interval_list boxes)
      (candle_cv_q_interval_list certificates) stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
   [candle_cv_q_packed_source_certificate_ordinary_step_def;
    LET_DEF; LET_END_DEF; candle_cv_analytic_instruction_def;
    cexp_ispair_def; cexp_fst_def; cexp_eq_def; cexp_if_def;
    injectivity "cval"; distinctness "cval"; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[cexp_if_def]);;

let candle_cv_q_packed_source_certificate_ordinary_sqrt_correct = prove
 (`!boxes source_sqrt certificates stack next certificate_rest.
    candle_q_packed_source_certificate_step boxes
      (Candle_analytic_program_sqrt source_sqrt)
      certificates stack next certificate_rest
    ==>
    candle_cv_q_packed_source_certificate_ordinary_step
      (candle_cv_q_interval_list boxes)
      (candle_cv_analytic_instruction
        (Candle_analytic_program_sqrt source_sqrt))
      (candle_cv_q_interval_list certificates)
      (candle_cv_q_dim_taylor_model_result_list_encode
        (candle_q_packed_source_item_results stack)) =
    candle_cv_q_packed_source_certificate_state T
      (candle_cv_q_dim_taylor_model_result_list_encode
        (candle_q_packed_source_item_results next))
      (candle_cv_q_interval_list certificate_rest)`,
  REPEAT GEN_TAC THEN DISCH_THEN (LABEL_TAC "certificate") THEN
  REWRITE_TAC[candle_cv_q_packed_source_certificate_ordinary_sqrt_select] THEN
  MATCH_MP_TAC candle_cv_q_packed_source_certificate_sqrt_step_refines THEN
  EXISTS_TAC `source_sqrt:((num#num)#num)#((num#num)#num)` THEN
  USE_THEN "certificate" ACCEPT_TAC);;

let candle_cv_q_packed_source_certificate_ordinary_atn_correct = prove
 (`!boxes certificates stack next certificate_rest.
    candle_q_packed_source_certificate_step boxes
      Candle_analytic_program_atn certificates stack next certificate_rest
    ==>
    candle_cv_q_packed_source_certificate_ordinary_step
      (candle_cv_q_interval_list boxes)
      (candle_cv_analytic_instruction Candle_analytic_program_atn)
      (candle_cv_q_interval_list certificates)
      (candle_cv_q_dim_taylor_model_result_list_encode
        (candle_q_packed_source_item_results stack)) =
    candle_cv_q_packed_source_certificate_state T
      (candle_cv_q_dim_taylor_model_result_list_encode
        (candle_q_packed_source_item_results next))
      (candle_cv_q_interval_list certificate_rest)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC
   [candle_cv_q_packed_source_certificate_ordinary_step_def;
    LET_DEF; LET_END_DEF; candle_cv_analytic_instruction_def;
    cexp_ispair_def; cexp_eq_def; cexp_if_def;
    injectivity "cval"; distinctness "cval"; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[cexp_if_def] THEN
  MATCH_MP_TAC candle_cv_q_packed_source_certificate_atn_step_refines THEN
  ASM_REWRITE_TAC[]);;

let candle_cv_q_packed_source_certificate_ordinary_correct = prove
 (`!boxes source certificates stack next certificate_rest.
    candle_q_packed_source_ordinary_certificate_step
      boxes source certificates stack next certificate_rest
    ==>
    candle_cv_q_packed_source_certificate_ordinary_step
      (candle_cv_q_interval_list boxes)
      (candle_cv_analytic_instruction source)
      (candle_cv_q_interval_list certificates)
      (candle_cv_q_dim_taylor_model_result_list_encode
        (candle_q_packed_source_item_results stack)) =
    candle_cv_q_packed_source_certificate_state T
      (candle_cv_q_dim_taylor_model_result_list_encode
        (candle_q_packed_source_item_results next))
      (candle_cv_q_interval_list certificate_rest)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_ordinary_certificate_step_def] THEN
  MESON_TAC
   [candle_cv_q_packed_source_certificate_ordinary_algebraic_correct;
    candle_cv_q_packed_source_certificate_ordinary_inv_correct;
    candle_cv_q_packed_source_certificate_ordinary_sqrt_correct;
    candle_cv_q_packed_source_certificate_ordinary_atn_correct]);;

let _ = print_endline "CANDLE_CERT_DISPATCH_STAGE ordinary-compute";;

(* A nonzero specialization code authenticates the exact source instruction  *)
(* before constructing its exact rational result.                            *)

let candle_cv_q_packed_source_certificate_specialized_step_def =
  new_definition
 `candle_cv_q_packed_source_certificate_specialized_step
      boxes code source certificates stack =
    Cexp_if (Cexp_eq code (Cexp_num 1))
      (Cexp_if
        (Cexp_eq source
          (candle_cv_analytic_instruction
            (Candle_analytic_push_poly
              (candle_poly_compile
                (candle_packed_delta_product_source_poly 0)))))
        (candle_cv_q_packed_source_certificate_state T
          (Cexp_pair
            (candle_cv_q_packed_delta_product_result boxes (Cexp_num 0))
            stack) certificates)
        (candle_cv_q_packed_source_certificate_failure stack certificates))
    (Cexp_if (Cexp_eq code (Cexp_num 2))
      (Cexp_if
        (Cexp_eq source
          (candle_cv_analytic_instruction
            (Candle_analytic_push_poly
              (candle_poly_compile
                (candle_packed_delta_product_source_poly 1)))))
        (candle_cv_q_packed_source_certificate_state T
          (Cexp_pair
            (candle_cv_q_packed_delta_product_result boxes (Cexp_num 1))
            stack) certificates)
        (candle_cv_q_packed_source_certificate_failure stack certificates))
    (Cexp_if (Cexp_eq code (Cexp_num 3))
      (Cexp_if
        (Cexp_eq source
          (candle_cv_analytic_instruction
            (Candle_analytic_push_poly
              (candle_poly_compile
                (candle_packed_delta_product_source_poly 2)))))
        (candle_cv_q_packed_source_certificate_state T
          (Cexp_pair
            (candle_cv_q_packed_delta_product_result boxes (Cexp_num 2))
            stack) certificates)
        (candle_cv_q_packed_source_certificate_failure stack certificates))
    (Cexp_if (Cexp_eq code (Cexp_num 4))
      (Cexp_if
        (Cexp_eq source
          (candle_cv_analytic_instruction
            (Candle_analytic_push_poly
              (candle_poly_compile
                (Candle_poly_neg
                  (candle_poly_diff 3 candle_packed_delta_poly))))))
        (candle_cv_q_packed_source_certificate_state T
          (Cexp_pair
            (candle_cv_q_packed_delta_neg_derivative_result
              boxes (Cexp_num 3)) stack) certificates)
        (candle_cv_q_packed_source_certificate_failure stack certificates))
    (Cexp_if (Cexp_eq code (Cexp_num 5))
      (Cexp_if
        (Cexp_eq source
          (candle_cv_analytic_instruction
            (Candle_analytic_push_poly
              (candle_poly_compile
                (Candle_poly_neg
                  (candle_poly_diff 4 candle_packed_delta_poly))))))
        (candle_cv_q_packed_source_certificate_state T
          (Cexp_pair
            (candle_cv_q_packed_delta_neg_derivative_result
              boxes (Cexp_num 4)) stack) certificates)
        (candle_cv_q_packed_source_certificate_failure stack certificates))
    (Cexp_if (Cexp_eq code (Cexp_num 6))
      (Cexp_if
        (Cexp_eq source
          (candle_cv_analytic_instruction
            (Candle_analytic_push_poly
              (candle_poly_compile
                (Candle_poly_neg
                  (candle_poly_diff 5 candle_packed_delta_poly))))))
        (candle_cv_q_packed_source_certificate_state T
          (Cexp_pair
            (candle_cv_q_packed_delta_neg_derivative_result
              boxes (Cexp_num 5)) stack) certificates)
        (candle_cv_q_packed_source_certificate_failure stack certificates))
      (candle_cv_q_packed_source_certificate_failure stack certificates))))))`;;

(* The specialized dispatcher uses numeral one as a successful comparison   *)
(* result.  Expose the corresponding branch reduction explicitly: the core  *)
(* cexp_if definition is phrased with SUC and does not by itself normalize   *)
(* the surface numeral in the executable-refinement proofs below.            *)

let candle_cv_q_packed_source_certificate_if_one = prove
 (`!positive negative. Cexp_if (Cexp_num 1) positive negative = positive`,
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; cexp_if_def]);;

(* The general negative-derivative result theorem is guarded by the supported *)
(* coordinate set.  These three closed instances keep that guard out of the  *)
(* dispatcher proof and document exactly which instruction codes are trusted. *)

let candle_cv_q_packed_delta_neg_derivative_result_3_correct = prove
 (`!boxes.
     candle_cv_q_packed_delta_neg_derivative_result
       (candle_cv_q_interval_list boxes) (Cexp_num 3) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_q_packed_delta_neg_derivative_result boxes 3)`,
  GEN_TAC THEN
  MATCH_MP_TAC candle_cv_q_packed_delta_neg_derivative_result_correct THEN
  REWRITE_TAC[]);;

let candle_cv_q_packed_delta_neg_derivative_result_4_correct = prove
 (`!boxes.
     candle_cv_q_packed_delta_neg_derivative_result
       (candle_cv_q_interval_list boxes) (Cexp_num 4) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_q_packed_delta_neg_derivative_result boxes 4)`,
  GEN_TAC THEN
  MATCH_MP_TAC candle_cv_q_packed_delta_neg_derivative_result_correct THEN
  REWRITE_TAC[]);;

let candle_cv_q_packed_delta_neg_derivative_result_5_correct = prove
 (`!boxes.
     candle_cv_q_packed_delta_neg_derivative_result
       (candle_cv_q_interval_list boxes) (Cexp_num 5) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_q_packed_delta_neg_derivative_result boxes 5)`,
  GEN_TAC THEN
  MATCH_MP_TAC candle_cv_q_packed_delta_neg_derivative_result_correct THEN
  REWRITE_TAC[]);;

let candle_cv_q_packed_source_certificate_specialized_product_correct = prove
 (`!boxes coordinate source certificates stack.
     candle_packed_delta_product_source_instruction coordinate source
     ==>
     candle_cv_q_packed_source_certificate_specialized_step
       (candle_cv_q_interval_list boxes) (Cexp_num (SUC coordinate))
       (candle_cv_analytic_instruction source)
       (candle_cv_q_interval_list certificates)
       (candle_cv_q_dim_taylor_model_result_list_encode
         (candle_q_packed_source_item_results stack)) =
     candle_cv_q_packed_source_certificate_state T
       (candle_cv_q_dim_taylor_model_result_list_encode
         (CONS (candle_q_packed_delta_product_result boxes coordinate)
           (candle_q_packed_source_item_results stack)))
       (candle_cv_q_interval_list certificates)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_packed_delta_product_source_instruction_def] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
    `coordinate = 0 \/ coordinate = 1 \/ coordinate = 2` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  ASM_REWRITE_TAC
   [candle_cv_q_packed_source_certificate_specialized_step_def;
    candle_cv_q_packed_delta_product_result_correct;
    candle_cv_q_dim_taylor_model_result_list_encode_def;
    cexp_eq_def; injectivity "cval"; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC
   [candle_cv_q_packed_source_certificate_if_one; cexp_if_def]);;

let candle_cv_q_packed_source_certificate_specialized_neg_correct = prove
 (`!boxes coordinate source certificates stack.
     candle_packed_delta_neg_derivative_source_instruction coordinate source
     ==>
     candle_cv_q_packed_source_certificate_specialized_step
       (candle_cv_q_interval_list boxes) (Cexp_num (SUC coordinate))
       (candle_cv_analytic_instruction source)
       (candle_cv_q_interval_list certificates)
       (candle_cv_q_dim_taylor_model_result_list_encode
         (candle_q_packed_source_item_results stack)) =
     candle_cv_q_packed_source_certificate_state T
       (candle_cv_q_dim_taylor_model_result_list_encode
         (CONS (candle_q_packed_delta_neg_derivative_result boxes coordinate)
           (candle_q_packed_source_item_results stack)))
       (candle_cv_q_interval_list certificates)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_packed_delta_neg_derivative_source_instruction_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "coordinate") ASSUME_TAC) THEN
  USE_THEN "coordinate" STRIP_ASSUME_TAC THEN
  ASM_REWRITE_TAC
   [candle_cv_q_packed_source_certificate_specialized_step_def;
    candle_cv_q_packed_delta_neg_derivative_result_3_correct;
    candle_cv_q_packed_delta_neg_derivative_result_4_correct;
    candle_cv_q_packed_delta_neg_derivative_result_5_correct;
    candle_cv_q_dim_taylor_model_result_list_encode_def;
    cexp_eq_def; injectivity "cval"; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC
   [candle_cv_q_packed_source_certificate_if_one; cexp_if_def]);;

let candle_cv_q_packed_source_certificate_specialized_product_branch = prove
 (`!boxes code source certificates stack next certificate_rest.
    (?coordinate.
       code = SUC coordinate /\ coordinate < 3 /\
       candle_packed_delta_product_source_instruction coordinate source /\
       next =
         CONS
           (candle_q_packed_source_item_make
             (candle_q_packed_delta_product_result boxes coordinate)
             (candle_packed_delta_product_source_expr coordinate)
             (candle_packed_delta_product_source_expr coordinate)) stack /\
       certificate_rest = certificates)
    ==>
    candle_cv_q_packed_source_certificate_specialized_step
      (candle_cv_q_interval_list boxes) (Cexp_num code)
      (candle_cv_analytic_instruction source)
      (candle_cv_q_interval_list certificates)
      (candle_cv_q_dim_taylor_model_result_list_encode
        (candle_q_packed_source_item_results stack)) =
    candle_cv_q_packed_source_certificate_state T
      (candle_cv_q_dim_taylor_model_result_list_encode
        (candle_q_packed_source_item_results next))
      (candle_cv_q_interval_list certificate_rest)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (X_CHOOSE_THEN `coordinate:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[candle_q_packed_source_item_results_make] THEN
  MATCH_MP_TAC
    candle_cv_q_packed_source_certificate_specialized_product_correct THEN
  ASM_REWRITE_TAC[]);;

let candle_cv_q_packed_source_certificate_specialized_neg_branch = prove
 (`!boxes code source certificates stack next certificate_rest.
    (?coordinate.
       code = SUC coordinate /\
       (coordinate = 3 \/ coordinate = 4 \/ coordinate = 5) /\
       candle_packed_delta_neg_derivative_source_instruction
         coordinate source /\
       next =
         CONS
           (candle_q_packed_source_item_make
             (candle_q_packed_delta_neg_derivative_result boxes coordinate)
             (candle_packed_delta_neg_derivative_expr coordinate)
             (candle_packed_delta_neg_derivative_expr coordinate)) stack /\
       certificate_rest = certificates)
    ==>
    candle_cv_q_packed_source_certificate_specialized_step
      (candle_cv_q_interval_list boxes) (Cexp_num code)
      (candle_cv_analytic_instruction source)
      (candle_cv_q_interval_list certificates)
      (candle_cv_q_dim_taylor_model_result_list_encode
        (candle_q_packed_source_item_results stack)) =
    candle_cv_q_packed_source_certificate_state T
      (candle_cv_q_dim_taylor_model_result_list_encode
        (candle_q_packed_source_item_results next))
      (candle_cv_q_interval_list certificate_rest)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (X_CHOOSE_THEN `coordinate:num`
      (CONJUNCTS_THEN2 (LABEL_TAC "code")
        (CONJUNCTS_THEN2 (LABEL_TAC "coordinate")
          (CONJUNCTS_THEN2 (LABEL_TAC "instruction")
            (CONJUNCTS_THEN2 (LABEL_TAC "next")
              (LABEL_TAC "certificates")))))) THEN
  USE_THEN "code" SUBST_ALL_TAC THEN
  USE_THEN "next" SUBST_ALL_TAC THEN
  USE_THEN "certificates" SUBST_ALL_TAC THEN
  REWRITE_TAC[candle_q_packed_source_item_results_make] THEN
  MATCH_MP_TAC
    candle_cv_q_packed_source_certificate_specialized_neg_correct THEN
  USE_THEN "instruction" ACCEPT_TAC);;

let candle_cv_q_packed_source_certificate_specialized_planned_correct = prove
 (`!boxes code source certificates stack next certificate_rest.
     candle_q_packed_source_planned_certificate_step
       boxes code source certificates stack next certificate_rest /\
     ~(code = 0)
     ==>
     candle_cv_q_packed_source_certificate_specialized_step
       (candle_cv_q_interval_list boxes) (Cexp_num code)
       (candle_cv_analytic_instruction source)
       (candle_cv_q_interval_list certificates)
       (candle_cv_q_dim_taylor_model_result_list_encode
         (candle_q_packed_source_item_results stack)) =
     candle_cv_q_packed_source_certificate_state T
       (candle_cv_q_dim_taylor_model_result_list_encode
         (candle_q_packed_source_item_results next))
       (candle_cv_q_interval_list certificate_rest)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_planned_certificate_step_def] THEN
  MESON_TAC
   [candle_cv_q_packed_source_certificate_specialized_product_branch;
    candle_cv_q_packed_source_certificate_specialized_neg_branch]);;

let _ = print_endline "CANDLE_CERT_DISPATCH_STAGE specialized-compute";;

let candle_cv_q_packed_source_certificate_dispatch_step_def = new_definition
 `candle_cv_q_packed_source_certificate_dispatch_step
      boxes code source certificates stack =
    Cexp_if (Cexp_eq code (Cexp_num 0))
      (candle_cv_q_packed_source_certificate_ordinary_step
        boxes source certificates stack)
      (candle_cv_q_packed_source_certificate_specialized_step
        boxes code source certificates stack)`;;

let candle_cv_q_packed_source_certificate_dispatch_planned_correct = prove
 (`!boxes code source certificates stack next certificate_rest.
    candle_q_packed_source_planned_certificate_step
      boxes code source certificates stack next certificate_rest
    ==>
    candle_cv_q_packed_source_certificate_dispatch_step
      (candle_cv_q_interval_list boxes) (Cexp_num code)
      (candle_cv_analytic_instruction source)
      (candle_cv_q_interval_list certificates)
      (candle_cv_q_dim_taylor_model_result_list_encode
        (candle_q_packed_source_item_results stack)) =
    candle_cv_q_packed_source_certificate_state T
      (candle_cv_q_dim_taylor_model_result_list_encode
        (candle_q_packed_source_item_results next))
      (candle_cv_q_interval_list certificate_rest)`,
  REPEAT GEN_TAC THEN DISCH_THEN (LABEL_TAC "planned") THEN
  ASM_CASES_TAC `code = 0` THENL
   [ASM_REWRITE_TAC
     [candle_cv_q_packed_source_certificate_dispatch_step_def;
      cexp_eq_def; cexp_if_def] THEN
    MATCH_MP_TAC candle_cv_q_packed_source_certificate_ordinary_correct THEN
    USE_THEN "planned" MP_TAC THEN
    REWRITE_TAC[candle_q_packed_source_planned_certificate_step_def] THEN
    ASM_REWRITE_TAC[NOT_SUC];
    ASM_REWRITE_TAC
     [candle_cv_q_packed_source_certificate_dispatch_step_def;
      cexp_eq_def; injectivity "cval"; cexp_if_def] THEN
    MATCH_MP_TAC
      candle_cv_q_packed_source_certificate_specialized_planned_correct THEN
    ASM_REWRITE_TAC[]]);;

let _ = print_endline "CANDLE_CERT_DISPATCH_STAGE dispatch-compute";;

let candle_cv_q_packed_source_certificate_dispatch_compute_eqs =
  union
    candle_cv_q_packed_source_delta_product_result_compute_eqs
    (map SPEC_ALL
      [candle_cv_q_packed_source_certificate_ordinary_step_def;
       candle_cv_q_packed_source_certificate_specialized_step_def;
       candle_cv_q_packed_source_certificate_dispatch_step_def]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_source_ordinary_step_source_step;
     candle_q_packed_source_ordinary_step_not_nonlinear;
     candle_q_packed_source_ordinary_step_certificate_step;
     candle_q_packed_source_ordinary_certificate_step_certificate_step;
     candle_q_packed_delta_product_planned_source_step;
     candle_q_packed_delta_neg_derivative_planned_source_step;
     candle_q_packed_delta_product_planned_certificate_step;
     candle_q_packed_delta_neg_derivative_planned_certificate_step;
     candle_q_packed_source_planned_certificate_step_source_step;
     candle_q_packed_source_item_results_poly;
     candle_q_packed_source_item_results_neg;
     candle_q_packed_source_item_results_add;
     candle_q_packed_source_item_results_mul;
     candle_q_packed_source_item_results_square;
     candle_q_packed_source_item_results_pi_half;
     candle_q_packed_source_item_results_make;
     candle_cv_q_packed_source_certificate_ordinary_algebraic_correct;
     candle_cv_q_packed_source_certificate_ordinary_inv_correct;
     candle_cv_q_packed_source_certificate_ordinary_sqrt_select;
     candle_cv_q_packed_source_certificate_ordinary_sqrt_correct;
     candle_cv_q_packed_source_certificate_ordinary_atn_correct;
     candle_cv_q_packed_source_certificate_ordinary_correct;
     candle_cv_q_packed_source_certificate_if_one;
     candle_cv_q_packed_delta_neg_derivative_result_3_correct;
     candle_cv_q_packed_delta_neg_derivative_result_4_correct;
     candle_cv_q_packed_delta_neg_derivative_result_5_correct;
     candle_cv_q_packed_source_certificate_specialized_product_correct;
     candle_cv_q_packed_source_certificate_specialized_neg_correct;
     candle_cv_q_packed_source_certificate_specialized_product_branch;
     candle_cv_q_packed_source_certificate_specialized_neg_branch;
     candle_cv_q_packed_source_certificate_specialized_planned_correct;
     candle_cv_q_packed_source_certificate_dispatch_planned_correct] then
  failwith "packed source certificate dispatch compute: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_CERTIFICATE_DISPATCH_DEFINITIONS_OK DEVELOPMENT_NON_RELEASE";;

end;;
