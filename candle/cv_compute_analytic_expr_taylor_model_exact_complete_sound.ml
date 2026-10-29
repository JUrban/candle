(* ========================================================================== *)
(* Scale-independent completion of an exact-rational Taylor model.          *)
(*                                                                            *)
(* The fast packed checker authenticates the Taylor center, whole-box        *)
(* Hessian, and radii independently.  These theorems assemble their exact    *)
(* value, gradient, and Hessian semantics without assuming that any of those *)
(* objects came from the canonical source-box construction.                  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_exact_gradient_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_exact_complete_sound = struct

open Multivariate_taylor;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_whole_box_dim_taylor_sound;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_analytic_expr_taylor_model_sound;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_semantics;;
open Candle_cv_analytic_expr_taylor_model_invariant;;
open Candle_cv_analytic_expr_taylor_model_exact_value_sound;;
open Candle_cv_analytic_expr_taylor_model_exact_gradient_sound;;

let candle_q_exact_taylor_model_complete_rounded_proxy_contains = prove
 (`!(f:real^N->real) (lower:real^N) (upper:real^N) (y:real^N)
       radii (domain:bool) center_jet hessian (p:real^N).
     LENGTH radii = dimindex (:N) /\
     ALL (\r. &0 <= candle_q_real r) radii /\
     m_cell_domain (lower,upper) y (candle_q_list_real_vector radii) /\
     diff2_domain (lower,upper) f /\
     candle_q_dim_jet_shape (dimindex (:N)) center_jet /\
     candle_q_dim_interval_matrix_shape (dimindex (:N)) hessian /\
     candle_q_interval_contains
       (candle_q_dim_jet_f center_jet) (f y) /\
     candle_q_stack_contains
       (candle_q_dim_jet_gradient center_jet)
       (list_of_seq
         (\di. partial (di + 1) f y)
         (dimindex (:N))) /\
     (!(z:real^N). z IN interval [lower,upper]
       ==> ALL2 candle_q_stack_contains hessian
             (list_of_seq
               (\di. list_of_seq
                 (\dj. partial2 (dj + 1) (di + 1) f z)
                 (dimindex (:N)))
               (dimindex (:N)))) /\
     p IN interval [lower,upper]
     ==>
     candle_q_dim_jet_contains_components (dimindex (:N))
       (candle_q_dim_taylor_model_proxy
         (candle_q_dim_taylor_model_result_complete_rounded
           radii domain center_jet hessian))
       (f p)
       (\di. partial (di + 1) f p)
       (\di dj. partial2 (dj + 1) (di + 1) f p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let components_rule =
    ISPECL
      [`dimindex (:N)`;
       `candle_q_dim_taylor_model_proxy
         (candle_q_dim_taylor_model_result_complete_rounded
           radii (domain:bool) center_jet hessian)`;
       `(f:real^N->real) p`;
       `(\di. partial (di + 1) (f:real^N->real) p):num->real`;
       `(\di dj. partial2 (dj + 1) (di + 1)
          (f:real^N->real) p):num->num->real`]
      candle_q_dim_jet_contains_components_of_stacks in
  let components_premise = fst (dest_imp (concl components_rule)) in
  SUBGOAL_THEN components_premise
    (fun components_th ->
      let assembled = BETA_RULE (MATCH_MP components_rule components_th) in
      MATCH_ACCEPT_TAC assembled) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[candle_q_dim_taylor_model_result_complete_rounded_def] THEN
    MATCH_MP_TAC candle_q_dim_taylor_model_proxy_make_shape THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_q_fixed_interval_list_round_length] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `LENGTH (candle_q_dim_jet_gradient center_jet)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC candle_q_dim_taylor_model_gradient_bounds_length THEN
        MP_TAC
          (REWRITE_RULE[candle_q_dim_jet_shape_def]
            (ASSUME
              `candle_q_dim_jet_shape (dimindex (:N)) center_jet`)) THEN
        MP_TAC
          (REWRITE_RULE[candle_q_dim_interval_matrix_shape_def]
            (ASSUME
              `candle_q_dim_interval_matrix_shape
                (dimindex (:N)) hessian`)) THEN
        MESON_TAC[];
        MP_TAC
          (REWRITE_RULE[candle_q_dim_jet_shape_def]
            (ASSUME
              `candle_q_dim_jet_shape (dimindex (:N)) center_jet`)) THEN
        MESON_TAC[]];
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[candle_q_dim_taylor_model_proxy_def;
                candle_q_dim_taylor_model_result_complete_rounded_def;
                candle_q_dim_taylor_model_result_make_def;
                candle_q_dim_taylor_model_result_value_bound_def;
                candle_q_dim_jet_make_def; candle_q_dim_jet_f_def;
                FST; SND] THEN
    MATCH_MP_TAC candle_q_fixed_interval_round_contains THEN
    MP_TAC
      (ISPECL
        [`f:real^N->real`; `lower:real^N`; `upper:real^N`; `y:real^N`;
         `radii:((num#num)#num)list`;
         `candle_q_dim_jet_f center_jet`;
         `candle_q_dim_jet_gradient center_jet`;
         `hessian:
            ((((num#num)#num)#((num#num)#num))list)list`;
         `p:real^N`]
        candle_q_exact_taylor_value_bound_contains) THEN
    ASM_REWRITE_TAC[candle_q_dim_taylor_model_value_bound_def;
                    candle_q_dim_taylor_model_error_def;
                    candle_q_dim_jet_make_def;
                    candle_q_dim_jet_f_def;
                    candle_q_dim_jet_gradient_def;
                    FST; SND];
    REWRITE_TAC[candle_q_dim_taylor_model_proxy_def;
                candle_q_dim_taylor_model_result_complete_rounded_def;
                candle_q_dim_taylor_model_result_make_def;
                candle_q_dim_taylor_model_result_gradient_bounds_def;
                candle_q_dim_jet_make_def; candle_q_dim_jet_gradient_def;
                FST; SND] THEN
    SUBGOAL_THEN
     `LENGTH (candle_q_dim_jet_gradient center_jet) = dimindex (:N)`
     ASSUME_TAC THENL
     [MP_TAC
        (REWRITE_RULE[candle_q_dim_jet_shape_def]
          (ASSUME
            `candle_q_dim_jet_shape (dimindex (:N)) center_jet`)) THEN
      MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `LENGTH
        (hessian:
          ((((num#num)#num)#((num#num)#num))list)list) = dimindex (:N)`
     ASSUME_TAC THENL
     [MP_TAC
        (REWRITE_RULE[candle_q_dim_interval_matrix_shape_def]
          (ASSUME
            `candle_q_dim_interval_matrix_shape (dimindex (:N)) hessian`)) THEN
      MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC
      (ISPECL
        [`f:real^N->real`; `lower:real^N`; `upper:real^N`; `y:real^N`;
         `radii:((num#num)#num)list`;
         `candle_q_dim_jet_gradient center_jet`;
         `hessian:
            ((((num#num)#num)#((num#num)#num))list)list`;
         `p:real^N`]
        candle_q_exact_taylor_gradient_bounds_contains) THEN
    ASM_REWRITE_TAC[candle_q_dim_jet_gradient_def];
    REWRITE_TAC[candle_q_dim_taylor_model_proxy_def;
                candle_q_dim_taylor_model_result_complete_rounded_def;
                candle_q_dim_taylor_model_result_make_def;
                candle_q_dim_taylor_model_result_hessian_def;
                candle_q_dim_jet_make_def; candle_q_dim_jet_hessian_def;
                FST; SND] THEN
    let hessian_at_p =
      MATCH_MP
        (SPEC `p:real^N`
          (ASSUME
            `!(z:real^N). z IN interval [lower,upper]
              ==> ALL2 candle_q_stack_contains hessian
                    (list_of_seq
                      (\di. list_of_seq
                        (\dj. partial2 (dj + 1) (di + 1)
                          (f:real^N->real) z)
                        (dimindex (:N)))
                      (dimindex (:N)))`))
        (ASSUME `(p:real^N) IN interval [lower,upper]`) in
    MATCH_ACCEPT_TAC (BETA_RULE hessian_at_p)]);;

let candle_q_exact_taylor_model_complete_proxy_contains = prove
 (`!(f:real^N->real) (lower:real^N) (upper:real^N) (y:real^N)
       radii (domain:bool) center_jet box_jet (p:real^N).
     LENGTH radii = dimindex (:N) /\
     ALL (\r. &0 <= candle_q_real r) radii /\
     m_cell_domain (lower,upper) y (candle_q_list_real_vector radii) /\
     diff2_domain (lower,upper) f /\
     candle_q_dim_jet_shape (dimindex (:N)) center_jet /\
     candle_q_dim_jet_shape (dimindex (:N)) box_jet /\
     candle_q_interval_contains
       (candle_q_dim_jet_f center_jet) (f y) /\
     candle_q_stack_contains
       (candle_q_dim_jet_gradient center_jet)
       (list_of_seq
         (\di. partial (di + 1) f y)
         (dimindex (:N))) /\
     (!(z:real^N). z IN interval [lower,upper]
       ==> ALL2 candle_q_stack_contains
             (candle_q_dim_jet_hessian box_jet)
             (list_of_seq
               (\di. list_of_seq
                 (\dj. partial2 (dj + 1) (di + 1) f z)
                 (dimindex (:N)))
               (dimindex (:N)))) /\
     p IN interval [lower,upper]
     ==>
     candle_q_dim_jet_contains_components (dimindex (:N))
       (candle_q_dim_taylor_model_proxy
         (candle_q_dim_taylor_model_result_complete
           radii domain center_jet (candle_q_dim_jet_hessian box_jet)))
       (f p)
       (\di. partial (di + 1) f p)
       (\di dj. partial2 (dj + 1) (di + 1) f p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_complete_def] THEN
  MATCH_MP_TAC
    (ISPECL
      [`f:real^N->real`; `lower:real^N`; `upper:real^N`; `y:real^N`;
       `radii:((num#num)#num)list`; `domain:bool`;
       `candle_q_dim_first_jet_fixed_round center_jet`;
       `candle_q_fixed_interval_matrix_round
          (candle_q_dim_jet_hessian box_jet)`;
       `p:real^N`]
      candle_q_exact_taylor_model_complete_rounded_proxy_contains) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_q_dim_first_jet_fixed_round_shape THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_q_fixed_interval_matrix_round_shape THEN
    ASM_MESON_TAC[candle_q_dim_jet_shape_def];
    REWRITE_TAC[candle_q_dim_first_jet_fixed_round_def;
                candle_q_dim_jet_make_def; candle_q_dim_jet_f_def;
                FST; SND] THEN
    MATCH_MP_TAC candle_q_fixed_interval_round_contains THEN
    MATCH_ACCEPT_TAC
      (REWRITE_RULE[candle_q_dim_jet_f_def]
        (ASSUME
          `candle_q_interval_contains
            (candle_q_dim_jet_f center_jet) ((f:real^N->real) y)`));
    REWRITE_TAC[candle_q_dim_first_jet_fixed_round_def;
                candle_q_dim_jet_make_def; candle_q_dim_jet_gradient_def;
                FST; SND] THEN
    MATCH_MP_TAC candle_q_fixed_interval_list_round_contains THEN
    MATCH_ACCEPT_TAC
      (REWRITE_RULE[candle_q_dim_jet_gradient_def]
        (ASSUME
          `candle_q_stack_contains
            (candle_q_dim_jet_gradient center_jet)
            (list_of_seq
              (\di. partial (di + 1) (f:real^N->real) y)
              (dimindex (:N)))`));
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC candle_q_fixed_interval_matrix_round_contains THEN
    ASM_MESON_TAC[];
    ASM_REWRITE_TAC[]]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_exact_taylor_model_complete_rounded_proxy_contains;
     candle_q_exact_taylor_model_complete_proxy_contains] then
  failwith "exact-rational Taylor completion soundness: assumptions";;

print_endline
  "CANDLE_CV_EXACT_TAYLOR_COMPLETE_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
