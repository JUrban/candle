(* ========================================================================== *)
(* Semantic erasure of analytic square-root certificate payloads.            *)
(*                                                                            *)
(* Square-root interval endpoints guide and authenticate numerical jet       *)
(* evaluation, but they are not part of the denoted source function or its   *)
(* first two derivatives.  Erasure gives a reusable logical identity for     *)
(* comparing center and whole-box programs carrying different certificates.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_calculus.ml";;

module Candle_cv_analytic_expr_certificate_erasure = struct

open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;

let candle_analytic_erase_sqrt_certificates_def = define
 `(candle_analytic_erase_sqrt_certificates (Candle_analytic_poly p) =
     Candle_analytic_poly p) /\
  (candle_analytic_erase_sqrt_certificates (Candle_analytic_neg a) =
     Candle_analytic_neg (candle_analytic_erase_sqrt_certificates a)) /\
  (candle_analytic_erase_sqrt_certificates (Candle_analytic_add a b) =
     Candle_analytic_add
       (candle_analytic_erase_sqrt_certificates a)
       (candle_analytic_erase_sqrt_certificates b)) /\
  (candle_analytic_erase_sqrt_certificates (Candle_analytic_mul a b) =
     Candle_analytic_mul
       (candle_analytic_erase_sqrt_certificates a)
       (candle_analytic_erase_sqrt_certificates b)) /\
  (candle_analytic_erase_sqrt_certificates (Candle_analytic_square a) =
     Candle_analytic_square (candle_analytic_erase_sqrt_certificates a)) /\
  (candle_analytic_erase_sqrt_certificates (Candle_analytic_inv a) =
     Candle_analytic_inv (candle_analytic_erase_sqrt_certificates a)) /\
  (candle_analytic_erase_sqrt_certificates
      (Candle_analytic_sqrt lp ln ld up un ud a) =
     Candle_analytic_sqrt 0 0 0 0 0 0
       (candle_analytic_erase_sqrt_certificates a)) /\
  (candle_analytic_erase_sqrt_certificates (Candle_analytic_atn a) =
     Candle_analytic_atn (candle_analytic_erase_sqrt_certificates a)) /\
  (candle_analytic_erase_sqrt_certificates Candle_analytic_pi_half =
     Candle_analytic_pi_half)`;;

let candle_analytic_erase_valid_dim = prove
 (`!e n.
     candle_analytic_valid_dim n
       (candle_analytic_erase_sqrt_certificates e) <=>
     candle_analytic_valid_dim n e`,
  MATCH_MP_TAC candle_analytic_expr_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def;
                  candle_analytic_valid_dim_def]);;

let candle_analytic_erase_value = prove
 (`!e env.
     candle_analytic_value env
       (candle_analytic_erase_sqrt_certificates e) =
     candle_analytic_value env e`,
  MATCH_MP_TAC candle_analytic_expr_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def;
                  candle_analytic_value_def]);;

let candle_analytic_erase_d = prove
 (`!e i env.
     candle_analytic_d i env
       (candle_analytic_erase_sqrt_certificates e) =
     candle_analytic_d i env e`,
  MATCH_MP_TAC candle_analytic_expr_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def;
                  candle_analytic_value_def; candle_analytic_d_def;
                  candle_analytic_erase_value]);;

let candle_analytic_erase_dd = prove
 (`!e i j env.
     candle_analytic_dd i j env
       (candle_analytic_erase_sqrt_certificates e) =
     candle_analytic_dd i j env e`,
  MATCH_MP_TAC candle_analytic_expr_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def;
                  candle_analytic_value_def; candle_analytic_d_def;
                  candle_analytic_dd_def; candle_analytic_erase_value;
                  candle_analytic_erase_d]);;

let candle_analytic_erase_denote_dim = prove
 (`!e.
     (candle_analytic_denote_dim
        (candle_analytic_erase_sqrt_certificates e):real^N->real) =
     candle_analytic_denote_dim e`,
  REWRITE_TAC[FUN_EQ_THM; candle_analytic_denote_dim_def;
              candle_analytic_erase_value]);;

let candle_q_dim_analytic_contains_erase = prove
 (`!n jet env e.
     candle_q_dim_analytic_contains n jet env
       (candle_analytic_erase_sqrt_certificates e) <=>
     candle_q_dim_analytic_contains n jet env e`,
  REWRITE_TAC[candle_q_dim_analytic_contains_def;
              candle_analytic_erase_value;
              candle_analytic_erase_d;
              candle_analytic_erase_dd]);;

let candle_q_dim_analytic_contains_certificate_transport = prove
 (`!n jet env center_e box_e.
     candle_analytic_erase_sqrt_certificates center_e =
     candle_analytic_erase_sqrt_certificates box_e
     ==> (candle_q_dim_analytic_contains n jet env center_e <=>
          candle_q_dim_analytic_contains n jet env box_e)`,
  MESON_TAC[candle_q_dim_analytic_contains_erase]);;

let candle_analytic_denote_certificate_transport = prove
 (`!center_e box_e.
     candle_analytic_erase_sqrt_certificates center_e =
     candle_analytic_erase_sqrt_certificates box_e
     ==> (candle_analytic_denote_dim center_e:real^N->real) =
         candle_analytic_denote_dim box_e`,
  MESON_TAC[candle_analytic_erase_denote_dim]);;

end;;
