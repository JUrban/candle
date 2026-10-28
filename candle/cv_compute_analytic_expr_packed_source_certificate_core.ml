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

(* The generic rational jet library already exposes the chain-rule lift with *)
(* an externally supplied reciprocal interval.  The lemmas below prove that *)
(* a checked certificate is exactly the missing premise for that constructor; *)
(* no second reciprocal implementation or per-expression calculus is needed. *)

let candle_q_dim_jet_inv_with_shape = prove
 (`!n reciprocal jet.
     candle_q_dim_jet_shape n jet
     ==> candle_q_dim_jet_shape n
           (candle_q_dim_jet_inv_with reciprocal jet)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_jet_inv_with_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_q_dim_interval_list_scale_length];
    MATCH_MP_TAC candle_q_dim_interval_matrix_add_shape THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_dim_interval_matrix_scale_shape THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC candle_q_dim_interval_matrix_scale_shape THEN
      MATCH_MP_TAC candle_q_dim_interval_outer_shape THEN
      ASM_REWRITE_TAC[]]]);;

let candle_q_dim_jet_inv_with_gradient_at = prove
 (`!n reciprocal jet i.
     candle_q_dim_jet_shape n jet /\ i < n
     ==>
     candle_q_dim_jet_gradient_at
       (candle_q_dim_jet_inv_with reciprocal jet) i =
     candle_q_interval_mul_normalized
       (candle_q_interval_neg
         (candle_q_interval_mul_normalized reciprocal reciprocal))
       (candle_q_dim_jet_gradient_at jet i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_jet_inv_with_def;
              candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_dim_interval_list_scale_lookup]);;

let candle_q_dim_jet_inv_with_hessian_at = prove
 (`!n reciprocal jet i j.
     candle_q_dim_jet_shape n jet /\ i < n /\ j < n
     ==>
     candle_q_dim_jet_hessian_at
       (candle_q_dim_jet_inv_with reciprocal jet) i j =
     candle_q_interval_add_normalized
       (candle_q_interval_mul_normalized
         (candle_q_interval_neg
           (candle_q_interval_mul_normalized reciprocal reciprocal))
         (candle_q_dim_jet_hessian_at jet i j))
       (candle_q_interval_mul_normalized
         (candle_q_interval_add_normalized
           (candle_q_interval_mul_normalized
             (candle_q_interval_mul_normalized reciprocal reciprocal)
             reciprocal)
           (candle_q_interval_mul_normalized
             (candle_q_interval_mul_normalized reciprocal reciprocal)
             reciprocal))
         (candle_q_interval_mul_normalized
           (candle_q_dim_jet_gradient_at jet i)
           (candle_q_dim_jet_gradient_at jet j)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_interval_matrix_shape_def;
              candle_q_dim_jet_inv_with_def;
              candle_q_dim_jet_hessian_at_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_dim_interval_matrix_add_row_lookup;
               candle_q_dim_interval_matrix_scale_row_lookup;
               candle_q_dim_interval_outer_row_lookup;
               candle_q_dim_interval_list_add_lookup;
               candle_q_dim_interval_list_scale_lookup;
               candle_q_dim_interval_matrix_add_map2; LENGTH_MAP2;
               candle_q_dim_interval_matrix_scale_map;
               candle_q_dim_interval_outer_map; LENGTH_MAP;
               candle_q_dim_interval_list_add_length;
               candle_q_dim_interval_list_scale_length;
               candle_q_dim_interval_rows_width_lookup_length]);;

let candle_q_interval_inv_certificate_square_sound = prove
 (`!input reciprocal x.
     candle_q_interval_inv_certificate input reciprocal /\
     candle_q_interval_contains input x
     ==>
     candle_q_interval_contains
       (candle_q_interval_mul_normalized reciprocal reciprocal)
       (inv x * inv x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_q_interval_contains reciprocal (inv x)`
   ASSUME_TAC THENL
   [ACCEPT_TAC
      (MATCH_MP
        (SPECL
          [`input:((num#num)#num)#((num#num)#num)`;
           `reciprocal:((num#num)#num)#((num#num)#num)`;
           `x:real`]
          candle_q_interval_inv_certificate_sound)
        (CONJ
          (ASSUME
            `candle_q_interval_inv_certificate input reciprocal`)
          (ASSUME `candle_q_interval_contains input x`)));
    ALL_TAC] THEN
  MATCH_MP_TAC candle_q_interval_mul_normalized_sound THEN
  ASM_REWRITE_TAC[]);;

let candle_q_interval_inv_certificate_square_neg_sound = prove
 (`!input reciprocal x.
     candle_q_interval_inv_certificate input reciprocal /\
     candle_q_interval_contains input x
     ==>
     candle_q_interval_contains
       (candle_q_interval_neg
         (candle_q_interval_mul_normalized reciprocal reciprocal))
       (--(inv x * inv x))`,
  MESON_TAC[candle_q_interval_inv_certificate_square_sound;
            candle_q_interval_neg_sound]);;

let candle_q_interval_inv_certificate_cube_sound = prove
 (`!input reciprocal x.
     candle_q_interval_inv_certificate input reciprocal /\
     candle_q_interval_contains input x
     ==>
     candle_q_interval_contains
       (candle_q_interval_mul_normalized
         (candle_q_interval_mul_normalized reciprocal reciprocal)
         reciprocal)
       ((inv x * inv x) * inv x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let premises = CONJ
    (ASSUME `candle_q_interval_inv_certificate input reciprocal`)
    (ASSUME `candle_q_interval_contains input x`) in
  let square_th = MATCH_MP
    (SPECL
      [`input:((num#num)#num)#((num#num)#num)`;
       `reciprocal:((num#num)#num)#((num#num)#num)`;
       `x:real`]
      candle_q_interval_inv_certificate_square_sound)
    premises in
  let reciprocal_th = MATCH_MP
    (SPECL
      [`input:((num#num)#num)#((num#num)#num)`;
       `reciprocal:((num#num)#num)#((num#num)#num)`;
       `x:real`]
      candle_q_interval_inv_certificate_sound)
    premises in
  ACCEPT_TAC
    (MATCH_MP
      (ISPECL
        [`candle_q_interval_mul_normalized reciprocal reciprocal`;
         `reciprocal:((num#num)#num)#((num#num)#num)`;
         `inv x * inv x`; `inv x`]
        candle_q_interval_mul_normalized_sound)
      (CONJ square_th reciprocal_th)));;

let candle_q_interval_inv_certificate_cube_twice_sound = prove
 (`!input reciprocal x.
     candle_q_interval_inv_certificate input reciprocal /\
     candle_q_interval_contains input x
     ==>
     candle_q_interval_contains
       (candle_q_interval_add_normalized
         (candle_q_interval_mul_normalized
           (candle_q_interval_mul_normalized reciprocal reciprocal)
           reciprocal)
         (candle_q_interval_mul_normalized
           (candle_q_interval_mul_normalized reciprocal reciprocal)
           reciprocal))
       (((inv x * inv x) * inv x) +
        ((inv x * inv x) * inv x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let cube_th = MATCH_MP
    (SPECL
      [`input:((num#num)#num)#((num#num)#num)`;
       `reciprocal:((num#num)#num)#((num#num)#num)`;
       `x:real`]
      candle_q_interval_inv_certificate_cube_sound)
    (CONJ
      (ASSUME `candle_q_interval_inv_certificate input reciprocal`)
      (ASSUME `candle_q_interval_contains input x`)) in
  ACCEPT_TAC
    (MATCH_MP
      (ISPECL
        [`candle_q_interval_mul_normalized
            (candle_q_interval_mul_normalized reciprocal reciprocal)
            reciprocal`;
         `candle_q_interval_mul_normalized
            (candle_q_interval_mul_normalized reciprocal reciprocal)
            reciprocal`;
         `(inv x * inv x) * inv x`;
         `(inv x * inv x) * inv x`]
        candle_q_interval_add_normalized_sound)
      (CONJ cube_th cube_th)));;

let candle_q_dim_jet_inv_with_components_sound = prove
 (`!n reciprocal jet value gradient hessian.
     candle_q_dim_jet_shape n jet /\
     candle_q_interval_inv_certificate
       (candle_q_dim_jet_f jet) reciprocal /\
     candle_q_dim_jet_contains_components n jet value gradient hessian
     ==>
     candle_q_dim_jet_contains_components n
       (candle_q_dim_jet_inv_with reciprocal jet)
       (inv value)
       (\i. (--(inv value * inv value)) * gradient i)
       (\i j.
          (--(inv value * inv value)) * hessian i j +
          (((inv value * inv value) * inv value) +
           ((inv value * inv value) * inv value)) *
          (gradient i * gradient j))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_contains_components_def] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[candle_q_dim_jet_inv_with_def;
                candle_q_dim_jet_f_def;
                candle_q_dim_jet_make_def; FST; SND] THEN
    ASM_MESON_TAC[candle_q_interval_inv_certificate_sound;
                  candle_q_dim_jet_contains_components_def];
    REPEAT STRIP_TAC THEN
    ASM_MESON_TAC[candle_q_dim_jet_inv_with_gradient_at;
                  candle_q_interval_mul_normalized_sound;
                  candle_q_interval_inv_certificate_square_neg_sound;
                  candle_q_dim_jet_contains_components_def];
    REPEAT STRIP_TAC THEN
    ASM_MESON_TAC[candle_q_dim_jet_inv_with_hessian_at;
                  candle_q_interval_add_normalized_sound;
                  candle_q_interval_mul_normalized_sound;
                  candle_q_interval_inv_certificate_square_neg_sound;
                  candle_q_interval_inv_certificate_cube_twice_sound;
                  candle_q_dim_jet_contains_components_def]]);;

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
     candle_cv_q_interval_inv_certificate_correct;
     candle_q_dim_jet_inv_with_shape;
     candle_q_dim_jet_inv_with_gradient_at;
     candle_q_dim_jet_inv_with_hessian_at;
     candle_q_interval_inv_certificate_square_sound;
     candle_q_interval_inv_certificate_square_neg_sound;
     candle_q_interval_inv_certificate_cube_sound;
     candle_q_interval_inv_certificate_cube_twice_sound;
     candle_q_dim_jet_inv_with_components_sound] then
  failwith "packed source certificate core: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_CERTIFICATE_CORE_OK DEVELOPMENT_NON_RELEASE";;

end;;
