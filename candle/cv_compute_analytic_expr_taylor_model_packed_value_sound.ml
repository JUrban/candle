(* ========================================================================== *)
(* Exact analytic handoff for a six-dimensional packed Taylor model.          *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The numerical checker stores only the 21      *)
(* upper-triangular Hessian intervals.  This theorem is the source-level      *)
(* contract that a registered checker result must satisfy: those packed       *)
(* intervals are expanded once, then the scale-independent exact Taylor       *)
(* theorem supplies the pointwise analytic bound.                             *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_exact_value_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_packed_hessian_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_packed_value_sound = struct

open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_hessian;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_exact_value_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_hessian_sound;;

let candle_q_packed_hessian6_exact_value_bound_contains = prove
 (`!e (lower:real^6) (upper:real^6) (y:real^6)
       radii center_value center_gradient packed (p:real^6).
     candle_analytic_valid_dim 6 e /\
     (!(z:real^6). z IN interval [lower,upper]
       ==> candle_analytic_regular_at
             (list_of_seq (\k. z$(k + 1)) 6) e) /\
     LENGTH radii = 6 /\
     ALL (\r. &0 <= candle_q_real r) radii /\
     m_cell_domain (lower,upper) y (candle_q_list_real_vector radii) /\
     diff2_domain (lower,upper) (candle_analytic_denote_dim e) /\
     candle_q_interval_contains center_value
       (candle_analytic_denote_dim e y) /\
     candle_q_stack_contains center_gradient
       (list_of_seq
         (\di. partial (di + 1) (candle_analytic_denote_dim e) y) 6) /\
     (!(z:real^6). z IN interval [lower,upper]
       ==> candle_q_stack_contains packed
             (candle_q_packed_hessian6_values
               (\i j. candle_analytic_dd i j
                 (list_of_seq (\k. z$(k + 1)) 6) e))) /\
     p IN interval [lower,upper]
     ==>
     candle_q_interval_contains
       (candle_q_dim_taylor_model_value_bound radii
         (candle_q_dim_jet_make center_value center_gradient
           (candle_q_packed_hessian6_expand packed))
         (candle_q_packed_hessian6_expand packed))
       (candle_analytic_denote_dim e p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC
   (ISPECL
     [`candle_analytic_denote_dim e:real^6->real`;
      `lower:real^6`; `upper:real^6`; `y:real^6`;
      `radii:((num#num)#num)list`;
      `center_value:((num#num)#num)#((num#num)#num)`;
      `center_gradient:
         (((num#num)#num)#((num#num)#num))list`;
      `candle_q_packed_hessian6_expand packed:
         ((((num#num)#num)#((num#num)#num))list)list`;
      `p:real^6`]
     candle_q_exact_taylor_value_bound_contains) THEN
  ASM_REWRITE_TAC[DIMINDEX_CONV `dimindex (:6)`] THEN
  X_GEN_TAC `z:real^6` THEN DISCH_TAC THEN
  MATCH_MP_TAC candle_q_packed_hessian6_analytic_partial2_contains THEN
  ASM_MESON_TAC[]);;

let candle_q_packed_hessian6_exact_cell_negative = prove
 (`!e (lower:real^6) (upper:real^6) (y:real^6)
       radii center_value center_gradient packed.
     candle_analytic_valid_dim 6 e /\
     (!(z:real^6). z IN interval [lower,upper]
       ==> candle_analytic_regular_at
             (list_of_seq (\k. z$(k + 1)) 6) e) /\
     LENGTH radii = 6 /\
     ALL (\r. &0 <= candle_q_real r) radii /\
     m_cell_domain (lower,upper) y (candle_q_list_real_vector radii) /\
     diff2_domain (lower,upper) (candle_analytic_denote_dim e) /\
     candle_q_interval_contains center_value
       (candle_analytic_denote_dim e y) /\
     candle_q_stack_contains center_gradient
       (list_of_seq
         (\di. partial (di + 1) (candle_analytic_denote_dim e) y) 6) /\
     (!(z:real^6). z IN interval [lower,upper]
       ==> candle_q_stack_contains packed
             (candle_q_packed_hessian6_values
               (\i j. candle_analytic_dd i j
                 (list_of_seq (\k. z$(k + 1)) 6) e))) /\
     candle_q_real
       (SND
         (candle_q_dim_taylor_model_value_bound radii
           (candle_q_dim_jet_make center_value center_gradient
             (candle_q_packed_hessian6_expand packed))
           (candle_q_packed_hessian6_expand packed))) < &0
     ==>
     !(p:real^6). p IN interval [lower,upper]
       ==> candle_analytic_denote_dim e p < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `p:real^6` THEN DISCH_TAC THEN
  MP_TAC
   (ISPECL
     [`e:candle_analytic_expr`;
      `lower:real^6`; `upper:real^6`; `y:real^6`;
      `radii:((num#num)#num)list`;
      `center_value:((num#num)#num)#((num#num)#num)`;
      `center_gradient:
         (((num#num)#num)#((num#num)#num))list`;
      `packed:(((num#num)#num)#((num#num)#num))list`;
      `p:real^6`]
     candle_q_packed_hessian6_exact_value_bound_contains) THEN
  ASM_REWRITE_TAC[candle_q_interval_contains_def] THEN
  ASM_REAL_ARITH_TAC);;

if hyp candle_q_packed_hessian6_exact_value_bound_contains <> [] ||
   hyp candle_q_packed_hessian6_exact_cell_negative <> [] then
  failwith "packed Hessian6 exact value soundness: assumptions";;

print_endline
  "CANDLE_CV_PACKED_HESSIAN6_EXACT_VALUE_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
