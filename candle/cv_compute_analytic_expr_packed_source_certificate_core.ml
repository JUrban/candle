(* ========================================================================== *)
(* Exact specification predicates for packed-source nonlinear certificates. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The fast word checker supplies outward-       *)
(* rounded intervals for nonlinear operations.  The ordinary Candle entry    *)
(* must validate those intervals against exact rational semantics before its  *)
(* acceptance theorem can imply facts about the original analytic source.    *)
(* This file starts that reusable specification layer with interval widening  *)
(* and reciprocal certificates.                                               *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_packed_hessian_sound.ml";;

module Candle_cv_analytic_expr_packed_source_certificate_core = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_exact_interval_inv_core;;
open Candle_cv_analytic_expr_program_compute;;

(* [outer] encloses every real value enclosed by [inner].  Endpoint validity *)
(* remains an explicit premise of consumers; the relation itself is the two  *)
(* exact ordering checks needed by certificate decoders.                      *)

let candle_q_interval_encloses_def = new_definition
 `candle_q_interval_encloses
      (outer:((num#num)#num)#((num#num)#num)) inner <=>
    candle_q_le (FST outer) (FST inner) /\
    candle_q_le (SND inner) (SND outer)`;;

let candle_q_interval_encloses_contains = prove
 (`!outer inner x.
     candle_q_interval_encloses outer inner /\
     candle_q_interval_contains inner x
     ==> candle_q_interval_contains outer x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_encloses_def;
              candle_q_interval_contains_def; candle_q_le_real] THEN
  REAL_ARITH_TAC);;

let candle_q_interval_encloses_refl = prove
 (`!interval. candle_q_interval_encloses interval interval`,
  GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_encloses_def; candle_q_le_real] THEN
  REAL_ARITH_TAC);;

let candle_q_interval_encloses_trans = prove
 (`!outer middle inner.
     candle_q_interval_encloses outer middle /\
     candle_q_interval_encloses middle inner
     ==> candle_q_interval_encloses outer inner`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_encloses_def; candle_q_le_real] THEN
  REAL_ARITH_TAC);;

let candle_cv_q_interval_encloses_def = new_definition
 `candle_cv_q_interval_encloses outer inner =
    candle_cv_bool_and
      (candle_cv_q_le (Cexp_fst outer) (Cexp_fst inner))
      (candle_cv_q_le (Cexp_snd inner) (Cexp_snd outer))`;;

let candle_cv_q_interval_encloses_correct = prove
 (`!outer inner.
     candle_cv_q_interval_encloses
       (candle_cv_q_interval outer) (candle_cv_q_interval inner) =
     candle_cv_bool (candle_q_interval_encloses outer inner)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_interval_encloses_def;
              candle_cv_q_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_q_le_correct; candle_cv_bool_and_def;
              candle_cv_bool_def; candle_q_interval_encloses_def] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[cexp_if_def]));;

(* A reciprocal certificate may be wider than the exact endpoint reciprocal. *)
(* This is the contract needed by the packed word evaluator: the fast checker *)
(* proves the widening relation, while the ordinary specification derives the *)
(* real reciprocal enclosure without repeating the word computation.         *)

let candle_q_interval_inv_certificate_def = new_definition
 `candle_q_interval_inv_certificate input output <=>
    candle_q_interval_not_zero input /\
    candle_q_interval_encloses output (candle_q_interval_inv input)`;;

let candle_q_interval_inv_certificate_sound = prove
 (`!input output x.
     candle_q_interval_inv_certificate input output /\
     candle_q_interval_contains input x
     ==> candle_q_interval_contains output (inv x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_inv_certificate_def] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC candle_q_interval_encloses_contains THEN
  EXISTS_TAC `candle_q_interval_inv input` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC candle_q_interval_inv_sound THEN
  ASM_REWRITE_TAC[]);;

let candle_cv_q_interval_inv_certificate_def = new_definition
 `candle_cv_q_interval_inv_certificate input output =
    candle_cv_bool_and
      (candle_cv_q_interval_not_zero input)
      (candle_cv_q_interval_encloses output
        (candle_cv_q_interval_inv input))`;;

let candle_cv_q_interval_inv_certificate_correct = prove
 (`!input output.
     candle_cv_q_interval_inv_certificate
       (candle_cv_q_interval input) (candle_cv_q_interval output) =
     candle_cv_bool (candle_q_interval_inv_certificate input output)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_interval_inv_certificate_def;
              candle_cv_q_interval_not_zero_correct;
              candle_cv_q_interval_inv_correct;
              candle_cv_q_interval_encloses_correct] THEN
  REWRITE_TAC[candle_q_interval_inv_certificate_def] THEN
  ASM_CASES_TAC `candle_q_interval_not_zero input` THEN
  ASM_REWRITE_TAC[candle_cv_bool_and_def; candle_cv_bool_def] THEN
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; cexp_if_def]);;

let candle_cv_q_packed_source_certificate_core_compute_eqs =
  map SPEC_ALL
    [candle_cv_q_interval_encloses_def;
     candle_cv_q_interval_inv_certificate_def];;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_interval_encloses_contains;
     candle_q_interval_encloses_refl;
     candle_q_interval_encloses_trans;
     candle_cv_q_interval_encloses_correct;
     candle_q_interval_inv_certificate_sound;
     candle_cv_q_interval_inv_certificate_correct] then
  failwith "packed source certificate core: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_CERTIFICATE_CORE_OK DEVELOPMENT_NON_RELEASE";;

end;;
