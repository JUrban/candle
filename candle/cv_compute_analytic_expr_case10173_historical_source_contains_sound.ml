(* ========================================================================== *)
(* Case-10173 historical production jet as an exact source-expression jet.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_source_dihedral_sound.ml";;

module Candle_cv_analytic_expr_case10173_historical_source_contains_sound = struct

open Candle_cv_analytic_dim_jet_inv;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_composition_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_reference_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_reference_instantiation;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_analytic_bridge_sound;;
open Candle_cv_analytic_expr_case10173_historical_source_polynomials_sound;;
open Candle_cv_analytic_expr_case10173_historical_source_jet_sound;;
open Candle_cv_analytic_expr_case10173_historical_source_dihedral_sound;;

let candle_hist_analytic_real_jet_value = prove
 (`!env expression.
     candle_hist_real_jet_value
       (candle_hist_analytic_real_jet env expression) =
     candle_analytic_value env expression`,
  REWRITE_TAC[candle_hist_analytic_real_jet_def;
              candle_hist_real_jet_make_def;
              candle_hist_real_jet_value_def; FST; SND]);;

let candle_hist_analytic_real_jet_gradient = prove
 (`!env expression coordinate.
     candle_hist_real_jet_gradient
       (candle_hist_analytic_real_jet env expression) coordinate =
     candle_analytic_d coordinate env expression`,
  REWRITE_TAC[candle_hist_analytic_real_jet_def;
              candle_hist_real_jet_make_def;
              candle_hist_real_jet_gradient_def; FST; SND]);;

let candle_hist_analytic_real_jet_hessian = prove
 (`!env expression rowindex colindex.
     candle_hist_real_jet_hessian
       (candle_hist_analytic_real_jet env expression)
       rowindex colindex =
     candle_analytic_dd rowindex colindex env expression`,
  REWRITE_TAC[candle_hist_analytic_real_jet_def;
              candle_hist_real_jet_make_def;
              candle_hist_real_jet_hessian_def; FST; SND]);;

(* Component-local congruence is the right boundary here: historical root
   records use six-entry lists, so their behavior outside coordinates 0--5
   is deliberately irrelevant. *)

let candle_real_hist_dihedral_value_congr = prove
 (`!delta_a root_delta_a root_four_a delta_b root_delta_b root_four_b.
     candle_hist_real_jet_value delta_a =
       candle_hist_real_jet_value delta_b /\
     candle_hist_real_jet_value root_delta_a =
       candle_hist_real_jet_value root_delta_b /\
     candle_hist_real_jet_value root_four_a =
       candle_hist_real_jet_value root_four_b
     ==> candle_hist_real_jet_value
           (candle_real_hist_dihedral_jet
             delta_a root_delta_a root_four_a) =
         candle_hist_real_jet_value
           (candle_real_hist_dihedral_jet
             delta_b root_delta_b root_four_b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[candle_real_hist_dihedral_jet_def;
                  candle_hist_real_jet_add_def;
                  candle_hist_real_jet_pi_half_def;
                  candle_hist_real_jet_atn_def;
                  candle_hist_real_jet_mul_def;
                  candle_hist_real_jet_neg_def;
                  candle_hist_real_jet_inv_def;
                  candle_hist_real_jet_make_def;
                  candle_hist_real_jet_value_def; FST; SND]);;

let candle_real_hist_dihedral_gradient_congr = prove
 (`!delta_a root_delta_a root_four_a delta_b root_delta_b root_four_b i.
     candle_hist_real_jet_value delta_a =
       candle_hist_real_jet_value delta_b /\
     candle_hist_real_jet_value root_delta_a =
       candle_hist_real_jet_value root_delta_b /\
     candle_hist_real_jet_value root_four_a =
       candle_hist_real_jet_value root_four_b /\
     candle_hist_real_jet_gradient delta_a i =
       candle_hist_real_jet_gradient delta_b i /\
     candle_hist_real_jet_gradient root_delta_a i =
       candle_hist_real_jet_gradient root_delta_b i /\
     candle_hist_real_jet_gradient root_four_a i =
       candle_hist_real_jet_gradient root_four_b i
     ==> candle_hist_real_jet_gradient
           (candle_real_hist_dihedral_jet
             delta_a root_delta_a root_four_a) i =
         candle_hist_real_jet_gradient
           (candle_real_hist_dihedral_jet
             delta_b root_delta_b root_four_b) i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC
   (REWRITE_RULE[candle_hist_real_jet_value_def;
                 candle_hist_real_jet_gradient_def]) THEN
  ASM_REWRITE_TAC[candle_real_hist_dihedral_jet_def;
                  candle_hist_real_jet_add_def;
                  candle_hist_real_jet_pi_half_def;
                  candle_hist_real_jet_atn_def;
                  candle_hist_real_jet_mul_def;
                  candle_hist_real_jet_neg_def;
                  candle_hist_real_jet_inv_def;
                  candle_hist_real_jet_make_def;
                  candle_hist_real_jet_value_def;
                  candle_hist_real_jet_gradient_def; FST; SND]);;

let candle_hist_real_jet_agree_at_def = new_definition
 `candle_hist_real_jet_agree_at i j left right <=>
    candle_hist_real_jet_value left = candle_hist_real_jet_value right /\
    candle_hist_real_jet_gradient left i =
      candle_hist_real_jet_gradient right i /\
    candle_hist_real_jet_gradient left j =
      candle_hist_real_jet_gradient right j /\
    candle_hist_real_jet_hessian left i j =
      candle_hist_real_jet_hessian right i j`;;

let candle_hist_real_jet_agree_at_refl = prove
 (`!i j jet. candle_hist_real_jet_agree_at i j jet jet`,
  REWRITE_TAC[candle_hist_real_jet_agree_at_def]);;

let candle_hist_real_jet_agree_at_neg = prove
 (`!i j left right.
     candle_hist_real_jet_agree_at i j left right
     ==> candle_hist_real_jet_agree_at i j
           (candle_hist_real_jet_neg left)
           (candle_hist_real_jet_neg right)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_hist_real_jet_agree_at_def;
              candle_hist_real_jet_neg_def;
              candle_hist_real_jet_make_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_hessian_def; FST; SND] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let candle_hist_real_jet_agree_at_add = prove
 (`!i j left_a right_a left_b right_b.
     candle_hist_real_jet_agree_at i j left_a left_b /\
     candle_hist_real_jet_agree_at i j right_a right_b
     ==> candle_hist_real_jet_agree_at i j
           (candle_hist_real_jet_add left_a right_a)
           (candle_hist_real_jet_add left_b right_b)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_hist_real_jet_agree_at_def;
              candle_hist_real_jet_add_def;
              candle_hist_real_jet_make_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_hessian_def; FST; SND] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let candle_hist_real_jet_agree_at_mul = prove
 (`!i j left_a right_a left_b right_b.
     candle_hist_real_jet_agree_at i j left_a left_b /\
     candle_hist_real_jet_agree_at i j right_a right_b
     ==> candle_hist_real_jet_agree_at i j
           (candle_hist_real_jet_mul left_a right_a)
           (candle_hist_real_jet_mul left_b right_b)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_hist_real_jet_agree_at_def;
              candle_hist_real_jet_mul_def;
              candle_hist_real_jet_make_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_hessian_def; FST; SND] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let candle_hist_real_jet_agree_at_inv = prove
 (`!i j left right.
     candle_hist_real_jet_agree_at i j left right
     ==> candle_hist_real_jet_agree_at i j
           (candle_hist_real_jet_inv left)
           (candle_hist_real_jet_inv right)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_hist_real_jet_agree_at_def;
              candle_hist_real_jet_inv_def;
              candle_hist_real_jet_make_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_hessian_def; FST; SND] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let candle_hist_real_jet_agree_at_atn = prove
 (`!i j left right.
     candle_hist_real_jet_agree_at i j left right
     ==> candle_hist_real_jet_agree_at i j
           (candle_hist_real_jet_atn left)
           (candle_hist_real_jet_atn right)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_hist_real_jet_agree_at_def;
              candle_hist_real_jet_atn_def;
              candle_hist_real_jet_make_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_hessian_def; FST; SND] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let candle_real_hist_dihedral_agree_at = prove
 (`!i j delta_a root_delta_a root_four_a delta_b root_delta_b root_four_b.
     candle_hist_real_jet_agree_at i j delta_a delta_b /\
     candle_hist_real_jet_agree_at i j root_delta_a root_delta_b /\
     candle_hist_real_jet_agree_at i j root_four_a root_four_b
     ==> candle_hist_real_jet_agree_at i j
           (candle_real_hist_dihedral_jet
             delta_a root_delta_a root_four_a)
           (candle_real_hist_dihedral_jet
             delta_b root_delta_b root_four_b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_real_hist_dihedral_jet_def] THEN
  MATCH_MP_TAC candle_hist_real_jet_agree_at_add THEN
  CONJ_TAC THENL
   [MATCH_ACCEPT_TAC candle_hist_real_jet_agree_at_refl;
    MATCH_MP_TAC candle_hist_real_jet_agree_at_atn THEN
    MATCH_MP_TAC candle_hist_real_jet_agree_at_mul THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_hist_real_jet_agree_at_neg THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC candle_hist_real_jet_agree_at_inv THEN
      MATCH_MP_TAC candle_hist_real_jet_agree_at_mul THEN
      ASM_REWRITE_TAC[]]]);;

let candle_real_hist_dihedral_hessian_congr = prove
 (`!delta_a root_delta_a root_four_a delta_b root_delta_b root_four_b i j.
     candle_hist_real_jet_value delta_a =
       candle_hist_real_jet_value delta_b /\
     candle_hist_real_jet_value root_delta_a =
       candle_hist_real_jet_value root_delta_b /\
     candle_hist_real_jet_value root_four_a =
       candle_hist_real_jet_value root_four_b /\
     candle_hist_real_jet_gradient delta_a i =
       candle_hist_real_jet_gradient delta_b i /\
     candle_hist_real_jet_gradient delta_a j =
       candle_hist_real_jet_gradient delta_b j /\
     candle_hist_real_jet_gradient root_delta_a i =
       candle_hist_real_jet_gradient root_delta_b i /\
     candle_hist_real_jet_gradient root_delta_a j =
       candle_hist_real_jet_gradient root_delta_b j /\
     candle_hist_real_jet_gradient root_four_a i =
       candle_hist_real_jet_gradient root_four_b i /\
     candle_hist_real_jet_gradient root_four_a j =
       candle_hist_real_jet_gradient root_four_b j /\
     candle_hist_real_jet_hessian delta_a i j =
       candle_hist_real_jet_hessian delta_b i j /\
     candle_hist_real_jet_hessian root_delta_a i j =
       candle_hist_real_jet_hessian root_delta_b i j /\
     candle_hist_real_jet_hessian root_four_a i j =
       candle_hist_real_jet_hessian root_four_b i j
     ==> candle_hist_real_jet_hessian
           (candle_real_hist_dihedral_jet
             delta_a root_delta_a root_four_a) i j =
         candle_hist_real_jet_hessian
           (candle_real_hist_dihedral_jet
             delta_b root_delta_b root_four_b) i j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
   (SPECL
     [`i:num`; `j:num`;
      `delta_a:real#((num->real)#(num->num->real))`;
      `root_delta_a:real#((num->real)#(num->num->real))`;
      `root_four_a:real#((num->real)#(num->num->real))`;
      `delta_b:real#((num->real)#(num->num->real))`;
      `root_delta_b:real#((num->real)#(num->num->real))`;
      `root_four_b:real#((num->real)#(num->num->real))`]
     candle_real_hist_dihedral_agree_at) THEN
  ASM_REWRITE_TAC[candle_hist_real_jet_agree_at_def] THEN
  MESON_TAC[]);;

let candle_case10173_hist_reference_separated_value = prove
 (`!values.
     candle_hist_real_jet_value
       (candle_fs_hist_reference_dihedral_real_jet values) =
     candle_hist_real_jet_value
       (candle_hist_analytic_real_jet (list_of_seq values 6)
         candle_case10173_hist_separated_dihedral_expr)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_reference_dihedral_real_jet_def;
              candle_case10173_hist_separated_dihedral_expr_def;
              GSYM candle_real_hist_dihedral_jet_is_analytic] THEN
  MATCH_MP_TAC candle_real_hist_dihedral_value_congr THEN
  REWRITE_TAC[candle_case10173_hist_delta_x4_jet_value;
              candle_case10173_hist_root_delta_jet_value;
              candle_case10173_hist_root_four_x0_jet_value;
              candle_hist_analytic_real_jet_value]);;

let candle_case10173_hist_reference_separated_d = prove
 (`!values coordinate.
     coordinate < 6
     ==> candle_hist_real_jet_gradient
           (candle_fs_hist_reference_dihedral_real_jet values) coordinate =
         candle_hist_real_jet_gradient
           (candle_hist_analytic_real_jet (list_of_seq values 6)
             candle_case10173_hist_separated_dihedral_expr) coordinate`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_reference_dihedral_real_jet_def;
              candle_case10173_hist_separated_dihedral_expr_def;
              GSYM candle_real_hist_dihedral_jet_is_analytic] THEN
  MATCH_MP_TAC candle_real_hist_dihedral_gradient_congr THEN
  REPEAT CONJ_TAC THEN
  ASM_SIMP_TAC[candle_case10173_hist_delta_x4_jet_value;
               candle_case10173_hist_root_delta_jet_value;
               candle_case10173_hist_root_four_x0_jet_value;
               candle_case10173_hist_delta_x4_jet_d;
               candle_case10173_hist_root_delta_jet_d;
               candle_case10173_hist_root_four_x0_jet_d;
               candle_hist_analytic_real_jet_value;
               candle_hist_analytic_real_jet_gradient]);;

let candle_case10173_hist_reference_separated_dd = prove
 (`!values rowindex colindex.
     rowindex < 6 /\ colindex < 6
     ==> candle_hist_real_jet_hessian
           (candle_fs_hist_reference_dihedral_real_jet values)
           rowindex colindex =
         candle_hist_real_jet_hessian
           (candle_hist_analytic_real_jet (list_of_seq values 6)
             candle_case10173_hist_separated_dihedral_expr)
           rowindex colindex`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_reference_dihedral_real_jet_def;
              candle_case10173_hist_separated_dihedral_expr_def;
              GSYM candle_real_hist_dihedral_jet_is_analytic] THEN
  MATCH_MP_TAC candle_real_hist_dihedral_hessian_congr THEN
  REPEAT CONJ_TAC THEN
  ASM_SIMP_TAC[candle_case10173_hist_delta_x4_jet_value;
               candle_case10173_hist_root_delta_jet_value;
               candle_case10173_hist_root_four_x0_jet_value;
               candle_case10173_hist_delta_x4_jet_d;
               candle_case10173_hist_root_delta_jet_d;
               candle_case10173_hist_root_four_x0_jet_d;
               candle_case10173_hist_delta_x4_jet_dd;
               candle_case10173_hist_root_delta_jet_dd;
               candle_case10173_hist_root_four_x0_jet_dd;
               candle_hist_analytic_real_jet_value;
               candle_hist_analytic_real_jet_gradient;
               candle_hist_analytic_real_jet_hessian]);;

let candle_case10173_hist_reference_source_value = prove
 (`!values lp ln ld up un ud.
     &0 < candle_fs_hist_delta_real values /\
     &0 < candle_fs_hist_four_x0_real values
     ==> candle_hist_real_jet_value
           (candle_fs_hist_reference_dihedral_real_jet values) =
         candle_analytic_value (list_of_seq values 6)
           (candle_case10173_hist_source_dihedral_expr
             lp ln ld up un ud)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `candle_hist_real_jet_value
      (candle_hist_analytic_real_jet (list_of_seq values 6)
        candle_case10173_hist_separated_dihedral_expr)` THEN
  CONJ_TAC THENL
   [MATCH_ACCEPT_TAC
      (SPEC `values:num->real`
        candle_case10173_hist_reference_separated_value);
    REWRITE_TAC[candle_hist_analytic_real_jet_value] THEN
    MP_TAC
      (SPECL
        [`list_of_seq (values:num->real) 6`;
         `lp:num`; `ln:num`; `ld:num`; `up:num`; `un:num`; `ud:num`]
        candle_case10173_hist_source_dihedral_real_jet) THEN
    ASM_REWRITE_TAC[candle_case10173_hist_delta_value;
                    candle_case10173_hist_four_x0_value] THEN
    DISCH_THEN
     (fun source_th ->
        let component_th =
          REWRITE_RULE[candle_hist_analytic_real_jet_value]
            (AP_TERM `candle_hist_real_jet_value` source_th) in
        MATCH_ACCEPT_TAC (GSYM component_th))]);;

let candle_case10173_hist_reference_source_d = prove
 (`!values lp ln ld up un ud coordinate.
     &0 < candle_fs_hist_delta_real values /\
     &0 < candle_fs_hist_four_x0_real values /\
     coordinate < 6
     ==> candle_hist_real_jet_gradient
           (candle_fs_hist_reference_dihedral_real_jet values) coordinate =
         candle_analytic_d coordinate (list_of_seq values 6)
           (candle_case10173_hist_source_dihedral_expr
             lp ln ld up un ud)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `candle_hist_real_jet_gradient
      (candle_hist_analytic_real_jet (list_of_seq values 6)
        candle_case10173_hist_separated_dihedral_expr) coordinate` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_case10173_hist_reference_separated_d THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_hist_analytic_real_jet_gradient] THEN
    MP_TAC
      (SPECL
        [`list_of_seq (values:num->real) 6`;
         `lp:num`; `ln:num`; `ld:num`; `up:num`; `un:num`; `ud:num`]
        candle_case10173_hist_source_dihedral_real_jet) THEN
    ASM_REWRITE_TAC[candle_case10173_hist_delta_value;
                    candle_case10173_hist_four_x0_value] THEN
    DISCH_THEN
     (fun source_th ->
        let component_th =
          REWRITE_RULE[candle_hist_analytic_real_jet_gradient]
            (AP_TERM
              `\jet:real#((num->real)#(num->num->real)).
                 candle_hist_real_jet_gradient jet coordinate`
              source_th) in
        MATCH_ACCEPT_TAC (GSYM component_th))]);;

let candle_case10173_hist_reference_source_dd = prove
 (`!values lp ln ld up un ud rowindex colindex.
     &0 < candle_fs_hist_delta_real values /\
     &0 < candle_fs_hist_four_x0_real values /\
     rowindex < 6 /\ colindex < 6
     ==> candle_hist_real_jet_hessian
           (candle_fs_hist_reference_dihedral_real_jet values)
           rowindex colindex =
         candle_analytic_dd rowindex colindex (list_of_seq values 6)
           (candle_case10173_hist_source_dihedral_expr
             lp ln ld up un ud)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `candle_hist_real_jet_hessian
      (candle_hist_analytic_real_jet (list_of_seq values 6)
        candle_case10173_hist_separated_dihedral_expr)
      rowindex colindex` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_case10173_hist_reference_separated_dd THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_hist_analytic_real_jet_hessian] THEN
    MP_TAC
      (SPECL
        [`list_of_seq (values:num->real) 6`;
         `lp:num`; `ln:num`; `ld:num`; `up:num`; `un:num`; `ud:num`]
        candle_case10173_hist_source_dihedral_real_jet) THEN
    ASM_REWRITE_TAC[candle_case10173_hist_delta_value;
                    candle_case10173_hist_four_x0_value] THEN
    DISCH_THEN
     (fun source_th ->
        let component_th =
          REWRITE_RULE[candle_hist_analytic_real_jet_hessian]
            (AP_TERM
              `\jet:real#((num->real)#(num->num->real)).
                 candle_hist_real_jet_hessian jet rowindex colindex`
              source_th) in
        MATCH_ACCEPT_TAC (GSYM component_th))]);;

let candle_case10173_hist_reference_source_contains = prove
 (`!jet values lp ln ld up un ud.
     &0 < candle_fs_hist_delta_real values /\
     &0 < candle_fs_hist_four_x0_real values /\
     candle_q_dim_jet_contains_components 6 jet
       (candle_hist_real_jet_value
         (candle_fs_hist_reference_dihedral_real_jet values))
       (candle_hist_real_jet_gradient
         (candle_fs_hist_reference_dihedral_real_jet values))
       (candle_hist_real_jet_hessian
         (candle_fs_hist_reference_dihedral_real_jet values))
     ==> candle_q_dim_analytic_contains 6 jet (list_of_seq values 6)
           (candle_case10173_hist_source_dihedral_expr
             lp ln ld up un ud)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_analytic_value (list_of_seq values 6)
      (candle_case10173_hist_source_dihedral_expr lp ln ld up un ud) =
    candle_hist_real_jet_value
      (candle_fs_hist_reference_dihedral_real_jet values)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC candle_case10173_hist_reference_source_value THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!coordinate.
      coordinate < 6
      ==> candle_analytic_d coordinate (list_of_seq values 6)
            (candle_case10173_hist_source_dihedral_expr
              lp ln ld up un ud) =
          candle_hist_real_jet_gradient
            (candle_fs_hist_reference_dihedral_real_jet values) coordinate`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC candle_case10173_hist_reference_source_d THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!rowindex colindex.
      rowindex < 6 /\ colindex < 6
      ==> candle_analytic_dd rowindex colindex (list_of_seq values 6)
            (candle_case10173_hist_source_dihedral_expr
              lp ln ld up un ud) =
          candle_hist_real_jet_hessian
            (candle_fs_hist_reference_dihedral_real_jet values)
            rowindex colindex`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC candle_case10173_hist_reference_source_dd THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[candle_q_dim_analytic_contains_def;
              candle_q_dim_jet_contains_components_def] THEN
  RULE_ASSUM_TAC
   (REWRITE_RULE[candle_q_dim_jet_contains_components_def]) THEN
  ASM_MESON_TAC[]);;

end;;
