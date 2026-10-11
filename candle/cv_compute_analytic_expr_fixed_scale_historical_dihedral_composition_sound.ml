(* ========================================================================== *)
(* Generic component composition for the historical dihedral expression.    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_root_four_x0_sound.ml";;
needs "candle/cv_compute_analytic_expr_jet.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_dihedral_composition_sound = struct

open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_delta_root_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_delta_x4_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_root_four_x0_sound;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_dim_jet_inv;;
open Candle_cv_analytic_dim_jet_pi_half;;
open Candle_cv_analytic_expr_jet;;

let candle_hist_real_jet_make_def = new_definition
 `candle_hist_real_jet_make (component_value:real)
      (component_gradient:num->real)
      (component_hessian:num->num->real) =
    (component_value,(component_gradient,component_hessian))`;;

let candle_hist_real_jet_value_def = new_definition
 `candle_hist_real_jet_value
      (hist_components:real#((num->real)#(num->num->real))) = FST hist_components`;;

let candle_hist_real_jet_gradient_def = new_definition
 `candle_hist_real_jet_gradient
      (hist_components:real#((num->real)#(num->num->real))) =
    FST (SND hist_components)`;;

let candle_hist_real_jet_hessian_def = new_definition
 `candle_hist_real_jet_hessian
      (hist_components:real#((num->real)#(num->num->real))) =
    SND (SND hist_components)`;;

let candle_hist_real_jet_neg_def = new_definition
 `candle_hist_real_jet_neg hist_components =
    candle_hist_real_jet_make
      (--(candle_hist_real_jet_value hist_components))
      (\i. --(candle_hist_real_jet_gradient hist_components i))
      (\i j. --(candle_hist_real_jet_hessian hist_components i j))`;;

let candle_hist_real_jet_add_def = new_definition
 `candle_hist_real_jet_add left right =
    candle_hist_real_jet_make
      (candle_hist_real_jet_value left + candle_hist_real_jet_value right)
      (\i.
         candle_hist_real_jet_gradient left i +
         candle_hist_real_jet_gradient right i)
      (\i j.
         candle_hist_real_jet_hessian left i j +
         candle_hist_real_jet_hessian right i j)`;;

let candle_hist_real_jet_mul_def = new_definition
 `candle_hist_real_jet_mul left right =
    candle_hist_real_jet_make
      (candle_hist_real_jet_value left * candle_hist_real_jet_value right)
      (\i.
         candle_hist_real_jet_gradient left i * candle_hist_real_jet_value right +
         candle_hist_real_jet_value left * candle_hist_real_jet_gradient right i)
      (\i j.
         (candle_hist_real_jet_hessian left i j *
            candle_hist_real_jet_value right +
          candle_hist_real_jet_gradient left i *
            candle_hist_real_jet_gradient right j) +
         (candle_hist_real_jet_gradient right i *
            candle_hist_real_jet_gradient left j +
          candle_hist_real_jet_value left *
            candle_hist_real_jet_hessian right i j))`;;

let candle_hist_real_jet_inv_def = new_definition
 `candle_hist_real_jet_inv hist_components =
    candle_hist_real_jet_make
      (inv (candle_hist_real_jet_value hist_components))
      (\i.
         (--(inv (candle_hist_real_jet_value hist_components) *
             inv (candle_hist_real_jet_value hist_components))) *
         candle_hist_real_jet_gradient hist_components i)
      (\i j.
         (--(inv (candle_hist_real_jet_value hist_components) *
             inv (candle_hist_real_jet_value hist_components))) *
           candle_hist_real_jet_hessian hist_components i j +
         (((inv (candle_hist_real_jet_value hist_components) *
             inv (candle_hist_real_jet_value hist_components)) *
            inv (candle_hist_real_jet_value hist_components)) +
          ((inv (candle_hist_real_jet_value hist_components) *
             inv (candle_hist_real_jet_value hist_components)) *
            inv (candle_hist_real_jet_value hist_components))) *
           (candle_hist_real_jet_gradient hist_components i *
            candle_hist_real_jet_gradient hist_components j))`;;

let candle_hist_real_jet_atn_def = new_definition
 `candle_hist_real_jet_atn hist_components =
    candle_hist_real_jet_make
      (atn (candle_hist_real_jet_value hist_components))
      (\i.
         inv (&1 + candle_hist_real_jet_value hist_components *
                   candle_hist_real_jet_value hist_components) *
         candle_hist_real_jet_gradient hist_components i)
      (\i j.
         (--((candle_hist_real_jet_value hist_components +
              candle_hist_real_jet_value hist_components) *
             (inv (&1 + candle_hist_real_jet_value hist_components *
                         candle_hist_real_jet_value hist_components) *
              inv (&1 + candle_hist_real_jet_value hist_components *
                         candle_hist_real_jet_value hist_components)))) *
           (candle_hist_real_jet_gradient hist_components i *
            candle_hist_real_jet_gradient hist_components j) +
         inv (&1 + candle_hist_real_jet_value hist_components *
                   candle_hist_real_jet_value hist_components) *
           candle_hist_real_jet_hessian hist_components i j)`;;

let candle_hist_real_jet_pi_half_def = new_definition
 `candle_hist_real_jet_pi_half =
    candle_hist_real_jet_make (pi / &2) (\i. &0) (\i j. &0)`;;

let candle_q_real_jet_neg_components_sound = prove
 (`!n jet hist_components.
     candle_q_dim_jet_shape n jet /\
     candle_q_dim_jet_contains_components n jet
       (candle_hist_real_jet_value hist_components)
       (candle_hist_real_jet_gradient hist_components)
       (candle_hist_real_jet_hessian hist_components)
     ==> candle_q_dim_jet_contains_components n
           (candle_q_dim_jet_normalized_neg jet)
           (candle_hist_real_jet_value (candle_hist_real_jet_neg hist_components))
           (candle_hist_real_jet_gradient (candle_hist_real_jet_neg hist_components))
           (candle_hist_real_jet_hessian (candle_hist_real_jet_neg hist_components))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_hist_real_jet_neg_def;
              candle_hist_real_jet_make_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_hessian_def; FST; SND] THEN
  MATCH_ACCEPT_TAC candle_q_dim_jet_neg_components_sound);;

let candle_q_real_jet_add_components_sound = prove
 (`!n left_jet right_jet left_components right_components.
     candle_q_dim_jet_shape n left_jet /\
     candle_q_dim_jet_shape n right_jet /\
     candle_q_dim_jet_contains_components n left_jet
       (candle_hist_real_jet_value left_components)
       (candle_hist_real_jet_gradient left_components)
       (candle_hist_real_jet_hessian left_components) /\
     candle_q_dim_jet_contains_components n right_jet
       (candle_hist_real_jet_value right_components)
       (candle_hist_real_jet_gradient right_components)
       (candle_hist_real_jet_hessian right_components)
     ==> candle_q_dim_jet_contains_components n
           (candle_q_dim_jet_normalized_add left_jet right_jet)
           (candle_hist_real_jet_value
             (candle_hist_real_jet_add left_components right_components))
           (candle_hist_real_jet_gradient
             (candle_hist_real_jet_add left_components right_components))
           (candle_hist_real_jet_hessian
             (candle_hist_real_jet_add left_components right_components))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_hist_real_jet_add_def;
              candle_hist_real_jet_make_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_hessian_def; FST; SND] THEN
  MATCH_ACCEPT_TAC candle_q_dim_jet_add_components_sound);;

let candle_q_real_jet_mul_components_sound = prove
 (`!n left_jet right_jet left_components right_components.
     candle_q_dim_jet_shape n left_jet /\
     candle_q_dim_jet_shape n right_jet /\
     candle_q_dim_jet_contains_components n left_jet
       (candle_hist_real_jet_value left_components)
       (candle_hist_real_jet_gradient left_components)
       (candle_hist_real_jet_hessian left_components) /\
     candle_q_dim_jet_contains_components n right_jet
       (candle_hist_real_jet_value right_components)
       (candle_hist_real_jet_gradient right_components)
       (candle_hist_real_jet_hessian right_components)
     ==> candle_q_dim_jet_contains_components n
           (candle_q_dim_jet_normalized_mul left_jet right_jet)
           (candle_hist_real_jet_value
             (candle_hist_real_jet_mul left_components right_components))
           (candle_hist_real_jet_gradient
             (candle_hist_real_jet_mul left_components right_components))
           (candle_hist_real_jet_hessian
             (candle_hist_real_jet_mul left_components right_components))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_hist_real_jet_mul_def;
              candle_hist_real_jet_make_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_hessian_def; FST; SND] THEN
  MATCH_ACCEPT_TAC candle_q_dim_jet_mul_components_sound);;

let candle_q_real_jet_inv_components_sound = prove
 (`!n jet hist_components.
     candle_q_dim_jet_shape n jet /\
     candle_q_dim_jet_inv_domain jet /\
     candle_q_dim_jet_contains_components n jet
       (candle_hist_real_jet_value hist_components)
       (candle_hist_real_jet_gradient hist_components)
       (candle_hist_real_jet_hessian hist_components)
     ==> candle_q_dim_jet_contains_components n
           (candle_q_dim_jet_inv jet)
           (candle_hist_real_jet_value (candle_hist_real_jet_inv hist_components))
           (candle_hist_real_jet_gradient (candle_hist_real_jet_inv hist_components))
           (candle_hist_real_jet_hessian (candle_hist_real_jet_inv hist_components))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_hist_real_jet_inv_def;
              candle_hist_real_jet_make_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_hessian_def; FST; SND] THEN
  MATCH_ACCEPT_TAC candle_q_dim_jet_inv_components_sound);;

let candle_q_real_jet_atn_components_sound = prove
 (`!n jet hist_components.
     candle_q_dim_jet_shape n jet /\
     candle_q_dim_jet_atn_domain jet /\
     candle_q_dim_jet_contains_components n jet
       (candle_hist_real_jet_value hist_components)
       (candle_hist_real_jet_gradient hist_components)
       (candle_hist_real_jet_hessian hist_components)
     ==> candle_q_dim_jet_contains_components n
           (candle_q_dim_jet_atn jet)
           (candle_hist_real_jet_value (candle_hist_real_jet_atn hist_components))
           (candle_hist_real_jet_gradient (candle_hist_real_jet_atn hist_components))
           (candle_hist_real_jet_hessian (candle_hist_real_jet_atn hist_components))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_hist_real_jet_atn_def;
              candle_hist_real_jet_make_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_hessian_def; FST; SND] THEN
  MATCH_ACCEPT_TAC candle_q_dim_jet_atn_components_sound);;

let candle_q_real_jet_pi_half_components_sound = prove
 (`!boxes.
     candle_q_dim_jet_contains_components (LENGTH boxes)
       (candle_q_dim_jet_pi_half boxes)
       (candle_hist_real_jet_value candle_hist_real_jet_pi_half)
       (candle_hist_real_jet_gradient candle_hist_real_jet_pi_half)
       (candle_hist_real_jet_hessian candle_hist_real_jet_pi_half)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_hist_real_jet_pi_half_def;
              candle_hist_real_jet_make_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_hessian_def; FST; SND] THEN
  MATCH_ACCEPT_TAC candle_q_dim_jet_pi_half_components_sound);;

let candle_q_hist_dihedral_jet_def = new_definition
 `candle_q_hist_dihedral_jet boxes delta_x4_jet root_delta root_four_x0 =
    candle_q_dim_jet_normalized_add
      (candle_q_dim_jet_pi_half boxes)
      (candle_q_dim_jet_atn
        (candle_q_dim_jet_normalized_mul
          (candle_q_dim_jet_normalized_neg delta_x4_jet)
          (candle_q_dim_jet_inv
            (candle_q_dim_jet_normalized_mul
              root_delta root_four_x0))))`;;

let candle_real_hist_dihedral_jet_def = new_definition
 `candle_real_hist_dihedral_jet delta_x4_jet root_delta root_four_x0 =
    candle_hist_real_jet_add candle_hist_real_jet_pi_half
      (candle_hist_real_jet_atn
        (candle_hist_real_jet_mul
          (candle_hist_real_jet_neg delta_x4_jet)
          (candle_hist_real_jet_inv
            (candle_hist_real_jet_mul root_delta root_four_x0))))`;;

let candle_q_hist_dihedral_jet_components_sound = prove
 (`!boxes delta_x4_jet root_delta root_four_x0
      delta_x4_components root_delta_components root_four_x0_components.
     LENGTH boxes = 6 /\
     candle_q_dim_jet_shape 6 delta_x4_jet /\
     candle_q_dim_jet_shape 6 root_delta /\
     candle_q_dim_jet_shape 6 root_four_x0 /\
     candle_q_dim_jet_contains_components 6 delta_x4_jet
       (candle_hist_real_jet_value delta_x4_components)
       (candle_hist_real_jet_gradient delta_x4_components)
       (candle_hist_real_jet_hessian delta_x4_components) /\
     candle_q_dim_jet_contains_components 6 root_delta
       (candle_hist_real_jet_value root_delta_components)
       (candle_hist_real_jet_gradient root_delta_components)
       (candle_hist_real_jet_hessian root_delta_components) /\
     candle_q_dim_jet_contains_components 6 root_four_x0
       (candle_hist_real_jet_value root_four_x0_components)
       (candle_hist_real_jet_gradient root_four_x0_components)
       (candle_hist_real_jet_hessian root_four_x0_components) /\
     candle_q_dim_jet_inv_domain
       (candle_q_dim_jet_normalized_mul root_delta root_four_x0) /\
     candle_q_dim_jet_atn_domain
       (candle_q_dim_jet_normalized_mul
         (candle_q_dim_jet_normalized_neg delta_x4_jet)
         (candle_q_dim_jet_inv
           (candle_q_dim_jet_normalized_mul root_delta root_four_x0)))
     ==>
     candle_q_dim_jet_contains_components 6
       (candle_q_hist_dihedral_jet
         boxes delta_x4_jet root_delta root_four_x0)
       (candle_hist_real_jet_value
         (candle_real_hist_dihedral_jet
           delta_x4_components root_delta_components
           root_four_x0_components))
       (candle_hist_real_jet_gradient
         (candle_real_hist_dihedral_jet
           delta_x4_components root_delta_components
           root_four_x0_components))
       (candle_hist_real_jet_hessian
         (candle_real_hist_dihedral_jet
           delta_x4_components root_delta_components
           root_four_x0_components))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_hist_dihedral_jet_def;
              candle_real_hist_dihedral_jet_def] THEN
  SUBGOAL_THEN
   `candle_q_dim_jet_shape 6
      (candle_q_dim_jet_normalized_mul root_delta root_four_x0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_dim_jet_normalized_mul_shape THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_dim_jet_contains_components 6
      (candle_q_dim_jet_normalized_mul root_delta root_four_x0)
      (candle_hist_real_jet_value
        (candle_hist_real_jet_mul root_delta_components
          root_four_x0_components))
      (candle_hist_real_jet_gradient
        (candle_hist_real_jet_mul root_delta_components
          root_four_x0_components))
      (candle_hist_real_jet_hessian
        (candle_hist_real_jet_mul root_delta_components
          root_four_x0_components))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_real_jet_mul_components_sound THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_dim_jet_shape 6
      (candle_q_dim_jet_inv
        (candle_q_dim_jet_normalized_mul root_delta root_four_x0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_dim_jet_inv_shape THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_dim_jet_contains_components 6
      (candle_q_dim_jet_inv
        (candle_q_dim_jet_normalized_mul root_delta root_four_x0))
      (candle_hist_real_jet_value
        (candle_hist_real_jet_inv
          (candle_hist_real_jet_mul root_delta_components
            root_four_x0_components)))
      (candle_hist_real_jet_gradient
        (candle_hist_real_jet_inv
          (candle_hist_real_jet_mul root_delta_components
            root_four_x0_components)))
      (candle_hist_real_jet_hessian
        (candle_hist_real_jet_inv
          (candle_hist_real_jet_mul root_delta_components
            root_four_x0_components)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_real_jet_inv_components_sound THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_dim_jet_shape 6
      (candle_q_dim_jet_normalized_neg delta_x4_jet)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_dim_jet_normalized_neg_shape THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_dim_jet_contains_components 6
      (candle_q_dim_jet_normalized_neg delta_x4_jet)
      (candle_hist_real_jet_value
        (candle_hist_real_jet_neg delta_x4_components))
      (candle_hist_real_jet_gradient
        (candle_hist_real_jet_neg delta_x4_components))
      (candle_hist_real_jet_hessian
        (candle_hist_real_jet_neg delta_x4_components))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_real_jet_neg_components_sound THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_dim_jet_shape 6
      (candle_q_dim_jet_normalized_mul
        (candle_q_dim_jet_normalized_neg delta_x4_jet)
        (candle_q_dim_jet_inv
          (candle_q_dim_jet_normalized_mul root_delta root_four_x0)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_dim_jet_normalized_mul_shape THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_dim_jet_contains_components 6
      (candle_q_dim_jet_normalized_mul
        (candle_q_dim_jet_normalized_neg delta_x4_jet)
        (candle_q_dim_jet_inv
          (candle_q_dim_jet_normalized_mul root_delta root_four_x0)))
      (candle_hist_real_jet_value
        (candle_hist_real_jet_mul
          (candle_hist_real_jet_neg delta_x4_components)
          (candle_hist_real_jet_inv
            (candle_hist_real_jet_mul root_delta_components
              root_four_x0_components))))
      (candle_hist_real_jet_gradient
        (candle_hist_real_jet_mul
          (candle_hist_real_jet_neg delta_x4_components)
          (candle_hist_real_jet_inv
            (candle_hist_real_jet_mul root_delta_components
              root_four_x0_components))))
      (candle_hist_real_jet_hessian
        (candle_hist_real_jet_mul
          (candle_hist_real_jet_neg delta_x4_components)
          (candle_hist_real_jet_inv
            (candle_hist_real_jet_mul root_delta_components
              root_four_x0_components))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_real_jet_mul_components_sound THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_dim_jet_shape 6
      (candle_q_dim_jet_atn
        (candle_q_dim_jet_normalized_mul
          (candle_q_dim_jet_normalized_neg delta_x4_jet)
          (candle_q_dim_jet_inv
            (candle_q_dim_jet_normalized_mul root_delta root_four_x0))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_dim_jet_atn_shape THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_dim_jet_contains_components 6
      (candle_q_dim_jet_atn
        (candle_q_dim_jet_normalized_mul
          (candle_q_dim_jet_normalized_neg delta_x4_jet)
          (candle_q_dim_jet_inv
            (candle_q_dim_jet_normalized_mul root_delta root_four_x0))))
      (candle_hist_real_jet_value
        (candle_hist_real_jet_atn
          (candle_hist_real_jet_mul
            (candle_hist_real_jet_neg delta_x4_components)
            (candle_hist_real_jet_inv
              (candle_hist_real_jet_mul root_delta_components
                root_four_x0_components)))))
      (candle_hist_real_jet_gradient
        (candle_hist_real_jet_atn
          (candle_hist_real_jet_mul
            (candle_hist_real_jet_neg delta_x4_components)
            (candle_hist_real_jet_inv
              (candle_hist_real_jet_mul root_delta_components
                root_four_x0_components)))))
      (candle_hist_real_jet_hessian
        (candle_hist_real_jet_atn
          (candle_hist_real_jet_mul
            (candle_hist_real_jet_neg delta_x4_components)
            (candle_hist_real_jet_inv
              (candle_hist_real_jet_mul root_delta_components
                root_four_x0_components)))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_real_jet_atn_components_sound THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC candle_q_real_jet_add_components_sound THEN
  ASM_MESON_TAC[candle_q_dim_jet_pi_half_shape;
                candle_q_real_jet_pi_half_components_sound]);;

end;;
