(* ========================================================================== *)
(* Genuine case-10173 source contract for the historical checked evaluator.  *)
(*                                                                            *)
(* The source has thirteen right-associated additive context operands, then  *)
(* the dihedral subexpression multiplied by minus one.  This unit proves the *)
(* structural splice contract once for arbitrary center/box sqrt payloads.   *)
(* It therefore does not reconstruct this source fact for every certificate  *)
(* leaf.                                                                      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_variable_batch_sound.ml";;

module Candle_cv_analytic_expr_case10173_historical_source_contract = struct

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_SOURCE_CONTRACT_PHASE begin";;

open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_certificate_patch;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_analytic_expr_case10173_historical_source_polynomials_sound;;
open Candle_cv_analytic_expr_case10173_historical_source_jet_sound;;
open Candle_cv_analytic_expr_case10173_historical_source_dihedral_sound;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_program_analytic_sound;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_program_logical_sound;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_variable_batch_sound;;

let candle_case10173_hist_source_factor_def = new_definition
 `candle_case10173_hist_source_factor =
    Candle_analytic_poly (Candle_poly_const 0 1 0)`;;

let candle_case10173_hist_source_context_def = new_definition
 `candle_case10173_hist_source_context =
   [(Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_const 1277 0 999)),
      Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_const 1277 0 999)));
    (Candle_analytic_mul
       (Candle_analytic_sqrt 2 0 0 3 0 0
         (Candle_analytic_poly (Candle_poly_var 0)))
       (Candle_analytic_poly (Candle_poly_const 136649 0 499999)),
     Candle_analytic_mul
       (Candle_analytic_sqrt 2 0 0 3 0 0
         (Candle_analytic_poly (Candle_poly_var 0)))
       (Candle_analytic_poly (Candle_poly_const 136649 0 499999)));
    (Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_mul (Candle_poly_const 136649 0 499999)
           (Candle_poly_neg (Candle_poly_const 109 0 49)))),
     Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_mul (Candle_poly_const 136649 0 499999)
           (Candle_poly_neg (Candle_poly_const 109 0 49)))));
    (Candle_analytic_mul
       (Candle_analytic_sqrt 2 0 0 3 0 0
         (Candle_analytic_poly (Candle_poly_var 1)))
       (Candle_analytic_poly
         (Candle_poly_neg (Candle_poly_const 273853 0 999999))),
     Candle_analytic_mul
       (Candle_analytic_sqrt 2 0 0 3 0 0
         (Candle_analytic_poly (Candle_poly_var 1)))
       (Candle_analytic_poly
         (Candle_poly_neg (Candle_poly_const 273853 0 999999))));
    (Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_mul (Candle_poly_const 273853 0 999999)
           (Candle_poly_const 2 0 0))),
     Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_mul (Candle_poly_const 273853 0 999999)
           (Candle_poly_const 2 0 0))));
    (Candle_analytic_mul
       (Candle_analytic_sqrt 2 0 0 3 0 0
         (Candle_analytic_poly (Candle_poly_var 2)))
       (Candle_analytic_poly
         (Candle_poly_neg (Candle_poly_const 273853 0 999999))),
     Candle_analytic_mul
       (Candle_analytic_sqrt 2 0 0 3 0 0
         (Candle_analytic_poly (Candle_poly_var 2)))
       (Candle_analytic_poly
         (Candle_poly_neg (Candle_poly_const 273853 0 999999))));
    (Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_mul (Candle_poly_const 273853 0 999999)
           (Candle_poly_const 2 0 0))),
     Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_mul (Candle_poly_const 273853 0 999999)
           (Candle_poly_const 2 0 0))));
    (Candle_analytic_mul
       (Candle_analytic_sqrt 2 0 0 3 0 0
         (Candle_analytic_poly (Candle_poly_var 3)))
       (Candle_analytic_poly (Candle_poly_const 354409 0 499999)),
     Candle_analytic_mul
       (Candle_analytic_sqrt 2 0 0 3 0 0
         (Candle_analytic_poly (Candle_poly_var 3)))
       (Candle_analytic_poly (Candle_poly_const 354409 0 499999)));
    (Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_mul (Candle_poly_const 354409 0 499999)
           (Candle_poly_neg (Candle_poly_const 2 0 0)))),
     Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_mul (Candle_poly_const 354409 0 499999)
           (Candle_poly_neg (Candle_poly_const 2 0 0)))));
    (Candle_analytic_mul
       (Candle_analytic_sqrt 2 0 0 3 0 0
         (Candle_analytic_poly (Candle_poly_var 4)))
       (Candle_analytic_poly
         (Candle_poly_neg (Candle_poly_const 78497 0 249999))),
     Candle_analytic_mul
       (Candle_analytic_sqrt 2 0 0 3 0 0
         (Candle_analytic_poly (Candle_poly_var 4)))
       (Candle_analytic_poly
         (Candle_poly_neg (Candle_poly_const 78497 0 249999))));
    (Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_mul (Candle_poly_const 78497 0 249999)
           (Candle_poly_const 2 0 0))),
     Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_mul (Candle_poly_const 78497 0 249999)
           (Candle_poly_const 2 0 0))));
    (Candle_analytic_mul
       (Candle_analytic_sqrt 2 0 0 3 0 0
         (Candle_analytic_poly (Candle_poly_var 5)))
       (Candle_analytic_poly
         (Candle_poly_neg (Candle_poly_const 78497 0 249999))),
     Candle_analytic_mul
       (Candle_analytic_sqrt 2 0 0 3 0 0
         (Candle_analytic_poly (Candle_poly_var 5)))
       (Candle_analytic_poly
         (Candle_poly_neg (Candle_poly_const 78497 0 249999))));
    (Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_mul (Candle_poly_const 78497 0 249999)
           (Candle_poly_const 2 0 0))),
     Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_mul (Candle_poly_const 78497 0 249999)
           (Candle_poly_const 2 0 0))))]`;;

let candle_case10173_hist_authenticated_source_def = new_definition
 `candle_case10173_hist_authenticated_source =
    candle_case10173_hist_context_box_expr
      candle_case10173_hist_source_context
      (candle_case10173_hist_source_dihedral_expr 50 0 0 100 0 0)
      candle_case10173_hist_source_factor`;;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_SOURCE_CONTRACT_PHASE source-defined";;

let candle_case10173_hist_patched_context_def = new_definition
 `candle_case10173_hist_patched_context c0 c1 c2 c3 c4 c5
      b0 b1 b2 b3 b4 b5 =
   [(Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_const 1277 0 999)),
     Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_const 1277 0 999)));
    (Candle_analytic_mul
       (candle_analytic_sqrt_with_interval c0
         (Candle_analytic_poly (Candle_poly_var 0)))
       (Candle_analytic_poly (Candle_poly_const 136649 0 499999)),
     Candle_analytic_mul
       (candle_analytic_sqrt_with_interval b0
         (Candle_analytic_poly (Candle_poly_var 0)))
       (Candle_analytic_poly (Candle_poly_const 136649 0 499999)));
    (Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_mul (Candle_poly_const 136649 0 499999)
           (Candle_poly_neg (Candle_poly_const 109 0 49)))),
     Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_mul (Candle_poly_const 136649 0 499999)
           (Candle_poly_neg (Candle_poly_const 109 0 49)))));
    (Candle_analytic_mul
       (candle_analytic_sqrt_with_interval c1
         (Candle_analytic_poly (Candle_poly_var 1)))
       (Candle_analytic_poly
         (Candle_poly_neg (Candle_poly_const 273853 0 999999))),
     Candle_analytic_mul
       (candle_analytic_sqrt_with_interval b1
         (Candle_analytic_poly (Candle_poly_var 1)))
       (Candle_analytic_poly
         (Candle_poly_neg (Candle_poly_const 273853 0 999999))));
    (Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_mul (Candle_poly_const 273853 0 999999)
           (Candle_poly_const 2 0 0))),
     Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_mul (Candle_poly_const 273853 0 999999)
           (Candle_poly_const 2 0 0))));
    (Candle_analytic_mul
       (candle_analytic_sqrt_with_interval c2
         (Candle_analytic_poly (Candle_poly_var 2)))
       (Candle_analytic_poly
         (Candle_poly_neg (Candle_poly_const 273853 0 999999))),
     Candle_analytic_mul
       (candle_analytic_sqrt_with_interval b2
         (Candle_analytic_poly (Candle_poly_var 2)))
       (Candle_analytic_poly
         (Candle_poly_neg (Candle_poly_const 273853 0 999999))));
    (Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_mul (Candle_poly_const 273853 0 999999)
           (Candle_poly_const 2 0 0))),
     Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_mul (Candle_poly_const 273853 0 999999)
           (Candle_poly_const 2 0 0))));
    (Candle_analytic_mul
       (candle_analytic_sqrt_with_interval c3
         (Candle_analytic_poly (Candle_poly_var 3)))
       (Candle_analytic_poly (Candle_poly_const 354409 0 499999)),
     Candle_analytic_mul
       (candle_analytic_sqrt_with_interval b3
         (Candle_analytic_poly (Candle_poly_var 3)))
       (Candle_analytic_poly (Candle_poly_const 354409 0 499999)));
    (Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_mul (Candle_poly_const 354409 0 499999)
           (Candle_poly_neg (Candle_poly_const 2 0 0)))),
     Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_mul (Candle_poly_const 354409 0 499999)
           (Candle_poly_neg (Candle_poly_const 2 0 0)))));
    (Candle_analytic_mul
       (candle_analytic_sqrt_with_interval c4
         (Candle_analytic_poly (Candle_poly_var 4)))
       (Candle_analytic_poly
         (Candle_poly_neg (Candle_poly_const 78497 0 249999))),
     Candle_analytic_mul
       (candle_analytic_sqrt_with_interval b4
         (Candle_analytic_poly (Candle_poly_var 4)))
       (Candle_analytic_poly
         (Candle_poly_neg (Candle_poly_const 78497 0 249999))));
    (Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_mul (Candle_poly_const 78497 0 249999)
           (Candle_poly_const 2 0 0))),
     Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_mul (Candle_poly_const 78497 0 249999)
           (Candle_poly_const 2 0 0))));
    (Candle_analytic_mul
       (candle_analytic_sqrt_with_interval c5
         (Candle_analytic_poly (Candle_poly_var 5)))
       (Candle_analytic_poly
         (Candle_poly_neg (Candle_poly_const 78497 0 249999))),
     Candle_analytic_mul
       (candle_analytic_sqrt_with_interval b5
         (Candle_analytic_poly (Candle_poly_var 5)))
       (Candle_analytic_poly
         (Candle_poly_neg (Candle_poly_const 78497 0 249999))));
    (Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_mul (Candle_poly_const 78497 0 249999)
           (Candle_poly_const 2 0 0))),
     Candle_analytic_poly
       (Candle_poly_mul (Candle_poly_const 1 0 0)
         (Candle_poly_mul (Candle_poly_const 78497 0 249999)
           (Candle_poly_const 2 0 0))))]`;;

(* Keep the concrete source proof linear in the thirteen-term context.  The
   generic patch definition otherwise repeatedly descends into these two
   recurring shapes while the simplifier is normalizing the full source. *)

let candle_case10173_hist_patch_context_sqrt_term = prove
 (`!i intervals lp ln ld up un ud p q.
     candle_analytic_patch_sqrt_certificates (CONS i intervals)
       (Candle_analytic_mul
         (Candle_analytic_sqrt lp ln ld up un ud
           (Candle_analytic_poly p))
         (Candle_analytic_poly q)) =
     (intervals,
      Candle_analytic_mul
        (candle_analytic_sqrt_with_interval i
          (Candle_analytic_poly p))
        (Candle_analytic_poly q))`,
  REWRITE_TAC
    [candle_analytic_patch_sqrt_certificates_def;
     candle_analytic_patch_sqrt_finish_def;
     LET_DEF;LET_END_DEF;FST;SND]);;

let candle_case10173_hist_patch_source_dihedral = prove
 (`!i intervals lp ln ld up un ud.
     candle_analytic_patch_sqrt_certificates (CONS i intervals)
       (candle_case10173_hist_source_dihedral_expr lp ln ld up un ud) =
     (intervals,
      candle_case10173_hist_source_dihedral_expr
        (FST (FST (FST i))) (SND (FST (FST i))) (SND (FST i))
        (FST (FST (SND i))) (SND (FST (SND i))) (SND (SND i)))`,
  REWRITE_TAC
    [candle_case10173_hist_source_dihedral_expr_def;
     candle_case10173_hist_source_numerator_expr_def;
     candle_case10173_hist_source_radical_expr_def;
     candle_analytic_patch_sqrt_certificates_def;
     candle_analytic_patch_sqrt_finish_def;
     candle_analytic_sqrt_with_interval_def;
     LET_DEF;LET_END_DEF;FST;SND]);;

let candle_case10173_hist_patch_poly = prove
 (`!intervals p.
     candle_analytic_patch_sqrt_certificates intervals
       (Candle_analytic_poly p) =
     (intervals,Candle_analytic_poly p)`,
  REWRITE_TAC[candle_analytic_patch_sqrt_certificates_def]);;

let candle_case10173_hist_patch_add_snd = prove
 (`!intervals left right.
     SND
       (candle_analytic_patch_sqrt_certificates intervals
         (Candle_analytic_add left right)) =
     Candle_analytic_add
       (SND (candle_analytic_patch_sqrt_certificates intervals left))
       (SND
         (candle_analytic_patch_sqrt_certificates
           (FST (candle_analytic_patch_sqrt_certificates intervals left))
           right))`,
  REWRITE_TAC
    [candle_analytic_patch_sqrt_certificates_def;
     LET_DEF;LET_END_DEF;FST;SND]);;

let candle_case10173_hist_patch_source_tail = prove
 (`!i intervals.
     candle_analytic_patch_sqrt_certificates (CONS i intervals)
       (Candle_analytic_mul
         (candle_case10173_hist_source_dihedral_expr 50 0 0 100 0 0)
         (Candle_analytic_poly (Candle_poly_const 0 1 0))) =
     (intervals,
      Candle_analytic_mul
        (candle_case10173_hist_source_dihedral_expr
          (FST (FST (FST i))) (SND (FST (FST i))) (SND (FST i))
          (FST (FST (SND i))) (SND (FST (SND i))) (SND (SND i)))
        (Candle_analytic_poly (Candle_poly_const 0 1 0)))`,
  REWRITE_TAC
    [candle_analytic_patch_sqrt_certificates_def;
     candle_case10173_hist_patch_source_dihedral;
     LET_DEF;LET_END_DEF;FST;SND]);;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_SOURCE_CONTRACT_PHASE patch-helpers";;

let candle_case10173_hist_authenticated_source_center_patch = prove
 (`!c0 c1 c2 c3 c4 c5 c6 b0 b1 b2 b3 b4 b5.
     SND
       (candle_analytic_patch_sqrt_certificates
         [c0;c1;c2;c3;c4;c5;c6]
         candle_case10173_hist_authenticated_source) =
     candle_case10173_hist_context_center_expr
       (candle_case10173_hist_patched_context
         c0 c1 c2 c3 c4 c5 b0 b1 b2 b3 b4 b5)
       (candle_case10173_hist_source_dihedral_expr
         (FST (FST (FST c6))) (SND (FST (FST c6))) (SND (FST c6))
         (FST (FST (SND c6))) (SND (FST (SND c6))) (SND (SND c6)))
       candle_case10173_hist_source_factor`,
  REPEAT GEN_TAC THEN
  PURE_REWRITE_TAC
    [candle_case10173_hist_authenticated_source_def;
     candle_case10173_hist_source_context_def;
     candle_case10173_hist_patched_context_def;
     candle_case10173_hist_source_factor_def;
     candle_case10173_hist_context_center_expr_def;
     candle_case10173_hist_context_box_expr_def] THEN
  REPLICATE_TAC 13
    (ONCE_REWRITE_TAC[candle_case10173_hist_patch_add_snd] THEN
     PURE_REWRITE_TAC
       [candle_case10173_hist_patch_poly;
        candle_case10173_hist_patch_context_sqrt_term;
        FST;SND]) THEN
  PURE_REWRITE_TAC[candle_case10173_hist_patch_source_tail;FST;SND] THEN
  REFL_TAC);;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_SOURCE_CONTRACT_PHASE center-patch";;

let candle_case10173_hist_authenticated_source_box_patch = prove
 (`!c0 c1 c2 c3 c4 c5 b0 b1 b2 b3 b4 b5 b6.
     SND
       (candle_analytic_patch_sqrt_certificates
         [b0;b1;b2;b3;b4;b5;b6]
         candle_case10173_hist_authenticated_source) =
     candle_case10173_hist_context_box_expr
       (candle_case10173_hist_patched_context
         c0 c1 c2 c3 c4 c5 b0 b1 b2 b3 b4 b5)
       (candle_case10173_hist_source_dihedral_expr
         (FST (FST (FST b6))) (SND (FST (FST b6))) (SND (FST b6))
         (FST (FST (SND b6))) (SND (FST (SND b6))) (SND (SND b6)))
       candle_case10173_hist_source_factor`,
  REPEAT GEN_TAC THEN
  PURE_REWRITE_TAC
    [candle_case10173_hist_authenticated_source_def;
     candle_case10173_hist_source_context_def;
     candle_case10173_hist_patched_context_def;
     candle_case10173_hist_source_factor_def;
     candle_case10173_hist_context_box_expr_def] THEN
  REPLICATE_TAC 13
    (ONCE_REWRITE_TAC[candle_case10173_hist_patch_add_snd] THEN
     PURE_REWRITE_TAC
       [candle_case10173_hist_patch_poly;
        candle_case10173_hist_patch_context_sqrt_term;
        FST;SND]) THEN
  PURE_REWRITE_TAC[candle_case10173_hist_patch_source_tail;FST;SND] THEN
  REFL_TAC);;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_SOURCE_CONTRACT_PHASE box-patch";;

let candle_case10173_hist_authenticated_source_compile_patch = prove
 (`!c0 c1 c2 c3 c4 c5 c6 b0 b1 b2 b3 b4 b5 b6.
     candle_analytic_compile
       (SND
         (candle_analytic_patch_sqrt_certificates
           [c0;c1;c2;c3;c4;c5;c6]
           candle_case10173_hist_authenticated_source)) =
       candle_analytic_compile
         (candle_case10173_hist_context_center_expr
           (candle_case10173_hist_patched_context
             c0 c1 c2 c3 c4 c5 b0 b1 b2 b3 b4 b5)
           (candle_case10173_hist_source_dihedral_expr
             (FST (FST (FST c6))) (SND (FST (FST c6))) (SND (FST c6))
             (FST (FST (SND c6))) (SND (FST (SND c6))) (SND (SND c6)))
           candle_case10173_hist_source_factor) /\
     candle_analytic_compile
       (SND
         (candle_analytic_patch_sqrt_certificates
           [b0;b1;b2;b3;b4;b5;b6]
           candle_case10173_hist_authenticated_source)) =
       candle_analytic_compile
         (candle_case10173_hist_context_box_expr
           (candle_case10173_hist_patched_context
             c0 c1 c2 c3 c4 c5 b0 b1 b2 b3 b4 b5)
           (candle_case10173_hist_source_dihedral_expr
             (FST (FST (FST b6))) (SND (FST (FST b6))) (SND (FST b6))
             (FST (FST (SND b6))) (SND (FST (SND b6))) (SND (SND b6)))
           candle_case10173_hist_source_factor)`,
  REPEAT GEN_TAC THEN
  CONJ_TAC THENL
   [PURE_REWRITE_TAC
      [candle_case10173_hist_authenticated_source_center_patch] THEN
    REFL_TAC;
    PURE_REWRITE_TAC
      [candle_case10173_hist_authenticated_source_box_patch] THEN
    REFL_TAC]);;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_SOURCE_CONTRACT_PHASE compile-patch";;

let candle_case10173_hist_patched_context_valid = prove
 (`!c0 c1 c2 c3 c4 c5 b0 b1 b2 b3 b4 b5.
     candle_case10173_hist_context_valid 6
       (candle_case10173_hist_patched_context
         c0 c1 c2 c3 c4 c5 b0 b1 b2 b3 b4 b5)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_case10173_hist_patched_context_def;
     candle_case10173_hist_source_context_def;
     candle_case10173_hist_context_valid_def;
     candle_analytic_patch_sqrt_certificates_def;
     candle_analytic_patch_sqrt_finish_def;
     candle_analytic_sqrt_with_interval_def;
     candle_analytic_valid_dim_def;
     candle_analytic_erase_sqrt_certificates_def;
     candle_poly_valid_dim_def;
     LET_DEF;LET_END_DEF;EL;HD;TL;FST;SND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_case10173_hist_context_center_compile = prove
 (`!context hole factor.
     candle_analytic_compile
       (candle_case10173_hist_context_center_expr context hole factor) =
     APPEND (candle_case10173_hist_context_center_prefix context)
       (APPEND (candle_analytic_compile hole)
         (candle_case10173_hist_context_center_suffix context factor))`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC
    [candle_case10173_hist_context_center_expr_def;
     candle_case10173_hist_context_center_prefix_def;
     candle_case10173_hist_context_center_suffix_def;
     candle_analytic_compile_def;APPEND;APPEND_ASSOC]);;

let candle_case10173_hist_context_box_compile = prove
 (`!context hole factor.
     candle_analytic_compile
       (candle_case10173_hist_context_box_expr context hole factor) =
     APPEND (candle_case10173_hist_context_box_prefix context)
       (APPEND (candle_analytic_compile hole)
         (candle_case10173_hist_context_box_suffix context factor))`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC
    [candle_case10173_hist_context_box_expr_def;
     candle_case10173_hist_context_box_prefix_def;
     candle_case10173_hist_context_box_suffix_def;
     candle_analytic_compile_def;APPEND;APPEND_ASSOC]);;

let candle_case10173_hist_source_dihedral_compile_eight = prove
 (`!lp ln ld up un ud.
     ?i0 i1 i2 i3 i4 i5 i6 i7.
       candle_analytic_compile
         (candle_case10173_hist_source_dihedral_expr
           lp ln ld up un ud) = [i0;i1;i2;i3;i4;i5;i6;i7]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_case10173_hist_source_dihedral_expr_def;
     candle_case10173_hist_source_numerator_expr_def;
     candle_case10173_hist_source_radical_expr_def;
     candle_analytic_compile_def;APPEND] THEN
  MESON_TAC[]);;

let candle_case10173_hist_patched_context_prefix_length = prove
 (`!c0 c1 c2 c3 c4 c5 b0 b1 b2 b3 b4 b5.
     LENGTH
       (candle_case10173_hist_context_center_prefix
         (candle_case10173_hist_patched_context
           c0 c1 c2 c3 c4 c5 b0 b1 b2 b3 b4 b5)) = 31 /\
     LENGTH
       (candle_case10173_hist_context_box_prefix
         (candle_case10173_hist_patched_context
           c0 c1 c2 c3 c4 c5 b0 b1 b2 b3 b4 b5)) = 31`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_case10173_hist_patched_context_def;
     candle_case10173_hist_source_context_def;
     candle_case10173_hist_context_center_prefix_def;
     candle_case10173_hist_context_box_prefix_def;
     candle_analytic_patch_sqrt_certificates_def;
     candle_analytic_patch_sqrt_finish_def;
     candle_analytic_sqrt_with_interval_def;
     candle_analytic_compile_def;
     LET_DEF;LET_END_DEF;APPEND;LENGTH;EL;HD;TL;FST;SND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_case10173_hist_patched_context_splice = prove
 (`!c0 c1 c2 c3 c4 c5 c6 b0 b1 b2 b3 b4 b5 b6.
     let context =
       candle_case10173_hist_patched_context
         c0 c1 c2 c3 c4 c5 b0 b1 b2 b3 b4 b5 in
     let center_hole =
       candle_case10173_hist_source_dihedral_expr
         (FST (FST (FST c6))) (SND (FST (FST c6))) (SND (FST c6))
         (FST (FST (SND c6))) (SND (FST (SND c6))) (SND (SND c6)) in
     let box_hole =
       candle_case10173_hist_source_dihedral_expr
         (FST (FST (FST b6))) (SND (FST (FST b6))) (SND (FST b6))
         (FST (FST (SND b6))) (SND (FST (SND b6))) (SND (SND b6)) in
     candle_cv_case10173_hist_splice_aux (Cexp_num 31)
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile
           (candle_case10173_hist_context_center_expr
             context center_hole candle_case10173_hist_source_factor))) =
       candle_cv_case10173_hist_program_of
         (candle_case10173_hist_context_center_prefix context)
         (candle_case10173_hist_context_center_suffix
           context candle_case10173_hist_source_factor) /\
     candle_cv_case10173_hist_splice_aux (Cexp_num 31)
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile
           (candle_case10173_hist_context_box_expr
             context box_hole candle_case10173_hist_source_factor))) =
       candle_cv_case10173_hist_program_of
         (candle_case10173_hist_context_box_prefix context)
         (candle_case10173_hist_context_box_suffix
           context candle_case10173_hist_source_factor)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF;LET_END_DEF] THEN
  REWRITE_TAC
    [candle_case10173_hist_context_center_compile;
     candle_case10173_hist_context_box_compile] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
      `31 =
       LENGTH
         (candle_case10173_hist_context_center_prefix
           (candle_case10173_hist_patched_context
             c0 c1 c2 c3 c4 c5 b0 b1 b2 b3 b4 b5))`
      SUBST1_TAC THENL
       [MESON_TAC[candle_case10173_hist_patched_context_prefix_length];
        ALL_TAC] THEN
    MESON_TAC
      [candle_case10173_hist_source_dihedral_compile_eight;
       candle_cv_case10173_hist_splice_segment];
    SUBGOAL_THEN
      `31 =
       LENGTH
         (candle_case10173_hist_context_box_prefix
           (candle_case10173_hist_patched_context
             c0 c1 c2 c3 c4 c5 b0 b1 b2 b3 b4 b5))`
      SUBST1_TAC THENL
       [MESON_TAC[candle_case10173_hist_patched_context_prefix_length];
        ALL_TAC] THEN
    MESON_TAC
      [candle_case10173_hist_source_dihedral_compile_eight;
       candle_cv_case10173_hist_splice_segment]]);;

let candle_case10173_hist_patched_context_center_splice =
  CONJUNCT1
    (SPEC_ALL
      (REWRITE_RULE[LET_DEF;LET_END_DEF]
        candle_case10173_hist_patched_context_splice));;

let candle_case10173_hist_patched_context_box_splice =
  CONJUNCT2
    (SPEC_ALL
      (REWRITE_RULE[LET_DEF;LET_END_DEF]
        candle_case10173_hist_patched_context_splice));;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_SOURCE_CONTRACT_PHASE splice";;

let candle_case10173_hist_source_factor_valid = prove
 (`candle_analytic_valid_dim 6 candle_case10173_hist_source_factor`,
  REWRITE_TAC
    [candle_case10173_hist_source_factor_def;
     candle_analytic_valid_dim_def;candle_poly_valid_dim_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_SOURCE_CONTRACT_PHASE factor-valid";;

let candle_case10173_hist_authenticated_source_patch_erasure = prove
 (`!c0 c1 c2 c3 c4 c5 b0 b1 b2 b3 b4 b5 b6.
     candle_analytic_erase_sqrt_certificates
       candle_case10173_hist_authenticated_source =
     candle_analytic_erase_sqrt_certificates
       (candle_case10173_hist_context_box_expr
         (candle_case10173_hist_patched_context
           c0 c1 c2 c3 c4 c5 b0 b1 b2 b3 b4 b5)
         (candle_case10173_hist_source_dihedral_expr
           (FST (FST (FST b6))) (SND (FST (FST b6))) (SND (FST b6))
           (FST (FST (SND b6))) (SND (FST (SND b6))) (SND (SND b6)))
         candle_case10173_hist_source_factor)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_case10173_hist_authenticated_source_def;
     candle_case10173_hist_source_context_def;
     candle_case10173_hist_patched_context_def;
     candle_case10173_hist_source_factor_def;
     candle_case10173_hist_context_box_expr_def;
     candle_case10173_hist_source_dihedral_expr_def;
     candle_case10173_hist_source_numerator_expr_def;
     candle_case10173_hist_source_radical_expr_def;
     candle_analytic_patch_sqrt_certificates_erasure;
     candle_analytic_sqrt_with_interval_def;
     candle_analytic_erase_sqrt_certificates_def;
     EL;FST;SND]);;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_SOURCE_CONTRACT_PHASE patch-erasure";;

let candle_case10173_hist_authenticated_job_source_contract = prove
 (`!c0 c1 c2 c3 c4 c5 c6 b0 b1 b2 b3 b4 b5 b6 boxes.
     LENGTH boxes = 6 /\ candle_q_box_valid_list boxes
     ==>
     candle_case10173_hist_job_source_contract
       candle_case10173_hist_authenticated_source
       ([b0;b1;b2;b3;b4;b5;b6],
        ([c0;c1;c2;c3;c4;c5;c6],boxes))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC
    [candle_case10173_hist_job_source_contract_def;
     LET_DEF;LET_END_DEF;FST;SND] THEN
  MAP_EVERY EXISTS_TAC
    [`candle_case10173_hist_patched_context
        c0 c1 c2 c3 c4 c5 b0 b1 b2 b3 b4 b5`;
     `candle_case10173_hist_source_factor`;
     `candle_case10173_hist_source_factor`;
     `FST (FST (FST
        (b6:((num#num)#num)#((num#num)#num))))`;
     `SND (FST (FST
        (b6:((num#num)#num)#((num#num)#num))))`;
     `SND (FST
        (b6:((num#num)#num)#((num#num)#num)))`;
     `FST (FST (SND
        (b6:((num#num)#num)#((num#num)#num))))`;
     `SND (FST (SND
        (b6:((num#num)#num)#((num#num)#num))))`;
     `SND (SND
        (b6:((num#num)#num)#((num#num)#num)))`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[candle_case10173_hist_patched_context_valid];
    REWRITE_TAC[candle_case10173_hist_source_factor_valid];
    REFL_TAC;
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    PURE_REWRITE_TAC
      [candle_case10173_hist_authenticated_source_center_patch] THEN
    REWRITE_TAC[candle_case10173_hist_patched_context_center_splice];
    PURE_REWRITE_TAC
      [candle_case10173_hist_authenticated_source_box_patch] THEN
    REWRITE_TAC[candle_case10173_hist_patched_context_box_splice];
    REWRITE_TAC
      [candle_case10173_hist_authenticated_source_patch_erasure]]);;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_SOURCE_CONTRACT_PHASE job-contract";;

(* The exact source expression has seven sqrt slots: six coordinate roots in
   the context followed by the dihedral radical. *)

let candle_case10173_hist_authenticated_source_sqrt_count = prove
 (`candle_analytic_sqrt_count
     candle_case10173_hist_authenticated_source = 7`,
  REWRITE_TAC
    [candle_case10173_hist_authenticated_source_def;
     candle_case10173_hist_source_context_def;
     candle_case10173_hist_source_factor_def;
     candle_case10173_hist_context_box_expr_def;
     candle_case10173_hist_source_dihedral_expr_def;
     candle_case10173_hist_source_numerator_expr_def;
     candle_case10173_hist_source_radical_expr_def;
     candle_analytic_sqrt_count_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_SOURCE_CONTRACT_OK DEVELOPMENT_NON_RELEASE";;

end;;
