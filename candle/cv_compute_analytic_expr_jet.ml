(* ========================================================================== *)
(* Universal nested analytic expressions for reflected nonlinear jets.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Polynomial regions remain compact shared-jet *)
(* leaves.  Arithmetic, reciprocal, and guarded square root compose those   *)
(* leaves without expression-specific calculus or arithmetic reconstruction. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_poly_inv.ml";;
needs "candle/cv_compute_analytic_poly_sqrt.ml";;

module Candle_cv_analytic_expr_jet = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_derivatives;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_dim_jet_inv;;
open Candle_cv_analytic_dim_jet_sqrt;;
open Candle_cv_analytic_poly_inv;;

let candle_analytic_expr_INDUCT,candle_analytic_expr_RECURSION = define_type
  "candle_analytic_expr =
       Candle_analytic_poly candle_poly_expr
     | Candle_analytic_neg candle_analytic_expr
     | Candle_analytic_add candle_analytic_expr candle_analytic_expr
     | Candle_analytic_mul candle_analytic_expr candle_analytic_expr
     | Candle_analytic_square candle_analytic_expr
     | Candle_analytic_inv candle_analytic_expr
     | Candle_analytic_sqrt num num num num num num candle_analytic_expr";;

let candle_analytic_sqrt_interval_def = new_definition
 `candle_analytic_sqrt_interval lp ln ld up un ud =
    (((lp,ln),ld),((up,un),ud))`;;

let candle_analytic_value_def = define
 `(candle_analytic_value env (Candle_analytic_poly p) =
     candle_poly_value_list env p) /\
  (candle_analytic_value env (Candle_analytic_neg a) =
     --(candle_analytic_value env a)) /\
  (candle_analytic_value env (Candle_analytic_add a b) =
     candle_analytic_value env a + candle_analytic_value env b) /\
  (candle_analytic_value env (Candle_analytic_mul a b) =
     candle_analytic_value env a * candle_analytic_value env b) /\
  (candle_analytic_value env (Candle_analytic_square a) =
     candle_analytic_value env a * candle_analytic_value env a) /\
  (candle_analytic_value env (Candle_analytic_inv a) =
     inv (candle_analytic_value env a)) /\
  (candle_analytic_value env
      (Candle_analytic_sqrt lp ln ld up un ud a) =
     sqrt (candle_analytic_value env a))`;;

let candle_analytic_d_def = define
 `(candle_analytic_d i env (Candle_analytic_poly p) =
     candle_poly_d_list i env p) /\
  (candle_analytic_d i env (Candle_analytic_neg a) =
     --(candle_analytic_d i env a)) /\
  (candle_analytic_d i env (Candle_analytic_add a b) =
     candle_analytic_d i env a + candle_analytic_d i env b) /\
  (candle_analytic_d i env (Candle_analytic_mul a b) =
     candle_analytic_d i env a * candle_analytic_value env b +
     candle_analytic_value env a * candle_analytic_d i env b) /\
  (candle_analytic_d i env (Candle_analytic_square a) =
     candle_analytic_d i env a * candle_analytic_value env a +
     candle_analytic_value env a * candle_analytic_d i env a) /\
  (candle_analytic_d i env (Candle_analytic_inv a) =
     (--(inv (candle_analytic_value env a) *
          inv (candle_analytic_value env a))) *
     candle_analytic_d i env a) /\
  (candle_analytic_d i env
      (Candle_analytic_sqrt lp ln ld up un ud a) =
     inv (sqrt (candle_analytic_value env a) +
          sqrt (candle_analytic_value env a)) *
     candle_analytic_d i env a)`;;

let candle_analytic_dd_def = define
 `(candle_analytic_dd i j env (Candle_analytic_poly p) =
     candle_poly_dd_list j i env p) /\
  (candle_analytic_dd i j env (Candle_analytic_neg a) =
     --(candle_analytic_dd i j env a)) /\
  (candle_analytic_dd i j env (Candle_analytic_add a b) =
     candle_analytic_dd i j env a + candle_analytic_dd i j env b) /\
  (candle_analytic_dd i j env (Candle_analytic_mul a b) =
     (candle_analytic_dd i j env a * candle_analytic_value env b +
      candle_analytic_d i env a * candle_analytic_d j env b) +
     (candle_analytic_d i env b * candle_analytic_d j env a +
      candle_analytic_value env a * candle_analytic_dd i j env b)) /\
  (candle_analytic_dd i j env (Candle_analytic_square a) =
     (candle_analytic_dd i j env a * candle_analytic_value env a +
      candle_analytic_d i env a * candle_analytic_d j env a) +
     (candle_analytic_d i env a * candle_analytic_d j env a +
      candle_analytic_value env a * candle_analytic_dd i j env a)) /\
  (candle_analytic_dd i j env (Candle_analytic_inv a) =
     (--(inv (candle_analytic_value env a) *
          inv (candle_analytic_value env a))) *
       candle_analytic_dd i j env a +
     (((inv (candle_analytic_value env a) *
         inv (candle_analytic_value env a)) *
        inv (candle_analytic_value env a)) +
       ((inv (candle_analytic_value env a) *
         inv (candle_analytic_value env a)) *
        inv (candle_analytic_value env a))) *
       (candle_analytic_d i env a * candle_analytic_d j env a)) /\
  (candle_analytic_dd i j env
      (Candle_analytic_sqrt lp ln ld up un ud a) =
     (--inv
       ((sqrt (candle_analytic_value env a) +
         sqrt (candle_analytic_value env a)) *
        (candle_analytic_value env a + candle_analytic_value env a))) *
       (candle_analytic_d i env a * candle_analytic_d j env a) +
     inv (sqrt (candle_analytic_value env a) +
          sqrt (candle_analytic_value env a)) *
       candle_analytic_dd i j env a)`;;

let candle_q_dim_analytic_jet_def = define
 `(candle_q_dim_analytic_jet boxes (Candle_analytic_poly p) =
     candle_q_dim_poly_jet_normalized boxes p) /\
  (candle_q_dim_analytic_jet boxes (Candle_analytic_neg a) =
     candle_q_dim_jet_normalized_neg
       (candle_q_dim_analytic_jet boxes a)) /\
  (candle_q_dim_analytic_jet boxes (Candle_analytic_add a b) =
     candle_q_dim_jet_normalized_add
       (candle_q_dim_analytic_jet boxes a)
       (candle_q_dim_analytic_jet boxes b)) /\
  (candle_q_dim_analytic_jet boxes (Candle_analytic_mul a b) =
     candle_q_dim_jet_normalized_mul
       (candle_q_dim_analytic_jet boxes a)
       (candle_q_dim_analytic_jet boxes b)) /\
  (candle_q_dim_analytic_jet boxes (Candle_analytic_square a) =
     candle_q_dim_jet_normalized_mul
       (candle_q_dim_analytic_jet boxes a)
       (candle_q_dim_analytic_jet boxes a)) /\
  (candle_q_dim_analytic_jet boxes (Candle_analytic_inv a) =
     candle_q_dim_jet_inv (candle_q_dim_analytic_jet boxes a)) /\
  (candle_q_dim_analytic_jet boxes
      (Candle_analytic_sqrt lp ln ld up un ud a) =
     candle_q_dim_jet_sqrt_with
       (candle_analytic_sqrt_interval lp ln ld up un ud)
       (candle_q_dim_analytic_jet boxes a))`;;

let candle_q_dim_analytic_domain_def = define
 `(candle_q_dim_analytic_domain boxes (Candle_analytic_poly p) <=> T) /\
  (candle_q_dim_analytic_domain boxes (Candle_analytic_neg a) <=>
     candle_q_dim_analytic_domain boxes a) /\
  (candle_q_dim_analytic_domain boxes (Candle_analytic_add a b) <=>
     candle_q_dim_analytic_domain boxes a /\
     candle_q_dim_analytic_domain boxes b) /\
  (candle_q_dim_analytic_domain boxes (Candle_analytic_mul a b) <=>
     candle_q_dim_analytic_domain boxes a /\
     candle_q_dim_analytic_domain boxes b) /\
  (candle_q_dim_analytic_domain boxes (Candle_analytic_square a) <=>
     candle_q_dim_analytic_domain boxes a) /\
  (candle_q_dim_analytic_domain boxes (Candle_analytic_inv a) <=>
     candle_q_dim_analytic_domain boxes a /\
     candle_q_dim_jet_inv_domain (candle_q_dim_analytic_jet boxes a)) /\
  (candle_q_dim_analytic_domain boxes
      (Candle_analytic_sqrt lp ln ld up un ud a) <=>
     candle_q_dim_analytic_domain boxes a /\
     candle_q_dim_jet_sqrt_domain
       (candle_analytic_sqrt_interval lp ln ld up un ud)
       (candle_q_dim_analytic_jet boxes a))`;;

let candle_q_dim_analytic_contains_def = new_definition
 `candle_q_dim_analytic_contains n jet env e <=>
    candle_q_dim_jet_contains_components n jet
      (candle_analytic_value env e)
      (\i. candle_analytic_d i env e)
      (\i j. candle_analytic_dd i j env e)`;;

let candle_q_dim_analytic_jet_shape = prove
 (`!e boxes.
     candle_q_dim_jet_shape (LENGTH boxes)
       (candle_q_dim_analytic_jet boxes e)`,
  MATCH_MP_TAC candle_analytic_expr_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[candle_q_dim_analytic_jet_def] THEN
  ASM_MESON_TAC[candle_q_dim_poly_jet_normalized_shape;
                candle_q_dim_jet_normalized_neg_shape;
                candle_q_dim_jet_normalized_add_shape;
                candle_q_dim_jet_normalized_mul_shape;
                candle_q_dim_jet_inv_shape;
                candle_q_dim_jet_sqrt_shape]);;

let candle_q_dim_jet_neg_components_sound = prove
 (`!n a value gradient hessian.
     candle_q_dim_jet_shape n a /\
     candle_q_dim_jet_contains_components n a value gradient hessian
     ==> candle_q_dim_jet_contains_components n
           (candle_q_dim_jet_normalized_neg a)
           (--value) (\i. --(gradient i)) (\i j. --(hessian i j))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_contains_components_def] THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[candle_q_dim_jet_f_def]) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_q_dim_jet_normalized_neg_def;
                candle_q_dim_jet_f_def;
                candle_q_dim_jet_make_def; FST; SND] THEN
    MATCH_MP_TAC candle_q_interval_neg_sound THEN ASM_REWRITE_TAC[];
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      ASM_MESON_TAC[candle_q_dim_jet_normalized_neg_gradient_at;
                    candle_q_interval_neg_sound];
      REPEAT STRIP_TAC THEN
      ASM_MESON_TAC[candle_q_dim_jet_normalized_neg_hessian_at;
                    candle_q_interval_neg_sound]]]);;

let candle_q_dim_jet_add_components_sound = prove
 (`!n a b va vb ga gb ha hb.
     candle_q_dim_jet_shape n a /\ candle_q_dim_jet_shape n b /\
     candle_q_dim_jet_contains_components n a va ga ha /\
     candle_q_dim_jet_contains_components n b vb gb hb
     ==> candle_q_dim_jet_contains_components n
           (candle_q_dim_jet_normalized_add a b)
           (va + vb) (\i. ga i + gb i) (\i j. ha i j + hb i j)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_contains_components_def] THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[candle_q_dim_jet_f_def]) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_q_dim_jet_normalized_add_def;
                candle_q_dim_jet_f_def;
                candle_q_dim_jet_make_def; FST; SND] THEN
    MATCH_MP_TAC candle_q_interval_add_normalized_sound THEN ASM_REWRITE_TAC[];
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      ASM_MESON_TAC[candle_q_dim_jet_normalized_add_gradient_at;
                    candle_q_interval_add_normalized_sound];
      REPEAT STRIP_TAC THEN
      ASM_MESON_TAC[candle_q_dim_jet_normalized_add_hessian_at;
                    candle_q_interval_add_normalized_sound]]]);;

let candle_q_dim_jet_mul_components_sound = prove
 (`!n a b va vb ga gb ha hb.
     candle_q_dim_jet_shape n a /\ candle_q_dim_jet_shape n b /\
     candle_q_dim_jet_contains_components n a va ga ha /\
     candle_q_dim_jet_contains_components n b vb gb hb
     ==> candle_q_dim_jet_contains_components n
           (candle_q_dim_jet_normalized_mul a b)
           (va * vb)
           (\i. ga i * vb + va * gb i)
           (\i j. (ha i j * vb + ga i * gb j) +
                  (gb i * ga j + va * hb i j))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_contains_components_def] THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[candle_q_dim_jet_f_def]) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_q_dim_jet_normalized_mul_def;
                candle_q_dim_jet_f_def;
                candle_q_dim_jet_make_def; FST; SND] THEN
    MATCH_MP_TAC candle_q_interval_mul_normalized_sound THEN ASM_REWRITE_TAC[];
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
       `candle_q_dim_jet_gradient_at
          (candle_q_dim_jet_normalized_mul a b) i =
        candle_q_interval_add_normalized
          (candle_q_interval_mul_normalized
            (candle_q_dim_jet_f b) (candle_q_dim_jet_gradient_at a i))
          (candle_q_interval_mul_normalized
            (candle_q_dim_jet_f a) (candle_q_dim_jet_gradient_at b i))`
      SUBST1_TAC THENL
       [MATCH_MP_TAC
          (SPEC `n:num` candle_q_dim_jet_normalized_mul_gradient_at) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[candle_q_dim_jet_f_def] THEN
        MATCH_MP_TAC candle_q_interval_add_normalized_sound THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC candle_q_interval_mul_normalized_sound_swapped THEN
          ASM_SIMP_TAC[];
          MATCH_MP_TAC candle_q_interval_mul_normalized_sound THEN
          ASM_SIMP_TAC[]]];
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
       `candle_q_dim_jet_hessian_at
          (candle_q_dim_jet_normalized_mul a b) i j =
        candle_q_interval_add_normalized
          (candle_q_interval_add_normalized
            (candle_q_interval_mul_normalized
              (candle_q_dim_jet_f b) (candle_q_dim_jet_hessian_at a i j))
            (candle_q_interval_mul_normalized
              (candle_q_dim_jet_gradient_at a i)
              (candle_q_dim_jet_gradient_at b j)))
          (candle_q_interval_add_normalized
            (candle_q_interval_mul_normalized
              (candle_q_dim_jet_gradient_at b i)
              (candle_q_dim_jet_gradient_at a j))
            (candle_q_interval_mul_normalized
              (candle_q_dim_jet_f a) (candle_q_dim_jet_hessian_at b i j)))`
      SUBST1_TAC THENL
       [MATCH_MP_TAC
          (SPEC `n:num` candle_q_dim_jet_normalized_mul_hessian_at) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[candle_q_dim_jet_f_def] THEN
        MATCH_MP_TAC candle_q_interval_add_normalized_sound THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC candle_q_interval_add_normalized_sound THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC candle_q_interval_mul_normalized_sound_swapped THEN
            ASM_SIMP_TAC[];
            MATCH_MP_TAC candle_q_interval_mul_normalized_sound THEN
            ASM_SIMP_TAC[]];
          MATCH_MP_TAC candle_q_interval_add_normalized_sound THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC candle_q_interval_mul_normalized_sound THEN
            ASM_SIMP_TAC[];
            MATCH_MP_TAC candle_q_interval_mul_normalized_sound THEN
            ASM_SIMP_TAC[]]]]]]);;

let candle_q_dim_analytic_jet_sound = prove
 (`!e boxes env.
     candle_q_stack_contains boxes env /\
     candle_q_dim_analytic_domain boxes e
     ==> candle_q_dim_analytic_contains (LENGTH boxes)
           (candle_q_dim_analytic_jet boxes e) env e`,
  MATCH_MP_TAC candle_analytic_expr_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[candle_q_dim_analytic_domain_def;
              candle_q_dim_analytic_jet_def;
              candle_q_dim_analytic_contains_def;
              candle_analytic_value_def;
              candle_analytic_d_def;
              candle_analytic_dd_def] THEN
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[GSYM candle_q_dim_poly_contains_components] THEN
    MATCH_MP_TAC candle_q_dim_poly_jet_normalized_sound THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_q_dim_jet_neg_components_sound THEN
    CONJ_TAC THENL
     [MATCH_ACCEPT_TAC candle_q_dim_analytic_jet_shape;
      REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def] THEN
      ASM_SIMP_TAC[]];
    MATCH_MP_TAC candle_q_dim_jet_add_components_sound THEN
    REPEAT CONJ_TAC THENL
      [MATCH_ACCEPT_TAC candle_q_dim_analytic_jet_shape;
       MATCH_ACCEPT_TAC candle_q_dim_analytic_jet_shape;
       REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def] THEN
       ASM_SIMP_TAC[];
       REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def] THEN
       ASM_SIMP_TAC[]];
    MATCH_MP_TAC candle_q_dim_jet_mul_components_sound THEN
    REPEAT CONJ_TAC THENL
      [MATCH_ACCEPT_TAC candle_q_dim_analytic_jet_shape;
       MATCH_ACCEPT_TAC candle_q_dim_analytic_jet_shape;
       REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def] THEN
       ASM_SIMP_TAC[];
       REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def] THEN
       ASM_SIMP_TAC[]];
    MATCH_MP_TAC candle_q_dim_jet_mul_components_sound THEN
    REPEAT CONJ_TAC THENL
      [MATCH_ACCEPT_TAC candle_q_dim_analytic_jet_shape;
       MATCH_ACCEPT_TAC candle_q_dim_analytic_jet_shape;
       REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def] THEN
       ASM_SIMP_TAC[];
       REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def] THEN
       ASM_SIMP_TAC[]];
    MATCH_MP_TAC candle_q_dim_jet_inv_components_sound THEN
    REPEAT CONJ_TAC THENL
     [MATCH_ACCEPT_TAC candle_q_dim_analytic_jet_shape;
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def] THEN
      ASM_SIMP_TAC[]];
    MATCH_MP_TAC candle_q_dim_jet_sqrt_components_sound THEN
    REPEAT CONJ_TAC THENL
     [MATCH_ACCEPT_TAC candle_q_dim_analytic_jet_shape;
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def] THEN
      ASM_SIMP_TAC[]]]);;

end;;
