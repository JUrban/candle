(* ========================================================================== *)
(* Focused reflected dimension-generic reciprocal-jet regression.            *)
(* ========================================================================== *)

load_path :=
  ["/project/worktrees/candle-cv-nonlinear-whole-box-v1"] @ !load_path;;

needs "candle/cv_compute_analytic_dim_jet_inv.ml";;

open Candle_cv_linear_combination_core;;
open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_exact_interval_inv_core;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_dim_jet_inv;;

let candle_q_dim_jet_inv_test_axioms_before = axioms ();;

let candle_q_dim_jet_inv_test_input =
 `candle_q_dim_jet_make
    (((2,0),0),((4,0),0))
    [(((1,0),0),((1,0),0))]
    [[(((0,0),0),((0,0),0))]]`;;

let candle_q_dim_jet_inv_test_crossing =
 `candle_q_dim_jet_make
    (((0,1),0),((2,0),0))
    [(((1,0),0),((1,0),0))]
    [[(((0,0),0),((0,0),0))]]`;;

let candle_q_dim_jet_inv_test_expected =
 `candle_q_dim_jet_make
    (((1,0),3),((1,0),1))
    [(((0,1),3),((0,1),15))]
    [[(((1,0),31),((1,0),3))]]`;;

let candle_q_dim_jet_inv_encode tm =
  rand
    (concl
      (REWRITE_CONV
        [candle_cv_q_dim_jet_encode_def;
         candle_cv_q_dim_jet_make_def;
         candle_cv_q_interval_matrix_def;
         candle_cv_q_interval_list_def;
         candle_cv_q_interval_def; candle_cv_q_def;
         candle_cv_lc_z_def;
         candle_q_dim_jet_make_def;
         candle_q_dim_jet_f_def;
         candle_q_dim_jet_gradient_def;
         candle_q_dim_jet_hessian_def; FST; SND]
        (mk_comb (`candle_cv_q_dim_jet_encode`,tm))));;

let candle_q_dim_jet_inv_test_computed =
  Kernel.compute
    (COMPUTE_INIT_THMS,candle_cv_q_dim_jet_inv_compute_eqs)
    (mk_comb
      (`candle_cv_q_dim_jet_inv`,
       candle_q_dim_jet_inv_encode candle_q_dim_jet_inv_test_input));;

let candle_q_dim_jet_inv_test_domain =
  Kernel.compute
    (COMPUTE_INIT_THMS,candle_cv_q_dim_jet_inv_compute_eqs)
    (mk_comb
      (`candle_cv_q_dim_jet_inv_domain`,
       candle_q_dim_jet_inv_encode candle_q_dim_jet_inv_test_input));;

let candle_q_dim_jet_inv_test_crossing_domain =
  Kernel.compute
    (COMPUTE_INIT_THMS,candle_cv_q_dim_jet_inv_compute_eqs)
    (mk_comb
      (`candle_cv_q_dim_jet_inv_domain`,
       candle_q_dim_jet_inv_encode candle_q_dim_jet_inv_test_crossing));;

if not
    (aconv (rand (concl candle_q_dim_jet_inv_test_computed))
      (candle_q_dim_jet_inv_encode candle_q_dim_jet_inv_test_expected)) ||
   not (aconv (rand (concl candle_q_dim_jet_inv_test_domain))
          `Cexp_num 1`) ||
   not (aconv (rand (concl candle_q_dim_jet_inv_test_crossing_domain))
          `Cexp_num 0`) then
  failwith "reflected reciprocal jet: computed result mismatch";;

let candle_q_dim_jet_inv_test_input_domain = prove
 (`candle_q_dim_jet_inv_domain
    (candle_q_dim_jet_make
      (((2,0),0),((4,0),0))
      [(((1,0),0),((1,0),0))]
      [[(((0,0),0),((0,0),0))]])`,
  REWRITE_TAC[candle_q_dim_jet_inv_domain_def;
              candle_q_dim_jet_f_def; candle_q_dim_jet_make_def;
              candle_q_interval_not_zero_def; candle_q_le_def;
              candle_q_zero_def; candle_q_den_def; FST; SND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_q_dim_jet_inv_test_input_shape = prove
 (`candle_q_dim_jet_shape 1
    (candle_q_dim_jet_make
      (((2,0),0),((4,0),0))
      [(((1,0),0),((1,0),0))]
      [[(((0,0),0),((0,0),0))]])`,
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_interval_matrix_shape_def;
              candle_q_dim_interval_rows_width_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; LENGTH; FST; SND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_q_dim_jet_inv_test_input_components = prove
 (`candle_q_dim_jet_contains_components 1
    (candle_q_dim_jet_make
      (((2,0),0),((4,0),0))
      [(((1,0),0),((1,0),0))]
      [[(((0,0),0),((0,0),0))]])
    (&3) (\i. &1) (\i j. &0)`,
  REWRITE_TAC[candle_q_dim_jet_contains_components_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_q_interval_contains_def; candle_q_real_def;
                candle_q_den_def; candle_lc_zreal_def; FST; SND] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `i = 0` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[candle_q_dim_jet_gradient_at_def;
                candle_q_dim_jet_gradient_def;
                candle_q_interval_lookup_def;
                candle_q_dim_jet_make_def;
                candle_q_interval_contains_def; candle_q_real_def;
                candle_q_den_def; candle_lc_zreal_def; FST; SND] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ARITH_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `i = 0` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `j = 0` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[candle_q_dim_jet_hessian_at_def;
                candle_q_dim_jet_hessian_def;
                candle_q_dim_interval_row_lookup_def;
                candle_q_interval_lookup_def;
                candle_q_dim_jet_make_def;
                candle_q_interval_contains_def; candle_q_real_def;
                candle_q_den_def; candle_lc_zreal_def; FST; SND] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ARITH_TAC]);;

let candle_q_dim_jet_inv_test_sound =
  MATCH_MP
    (SPECL
      [`1`; candle_q_dim_jet_inv_test_input; `&3:real`;
       `(\i. &1):num->real`; `(\i j. &0):num->num->real`]
      candle_q_dim_jet_inv_components_sound)
    (CONJ candle_q_dim_jet_inv_test_input_shape
      (CONJ candle_q_dim_jet_inv_test_input_domain
        candle_q_dim_jet_inv_test_input_components));;

if hyp candle_q_dim_jet_inv_test_computed <> [] ||
   hyp candle_q_dim_jet_inv_test_domain <> [] ||
   hyp candle_q_dim_jet_inv_test_crossing_domain <> [] ||
   hyp candle_q_dim_jet_inv_test_sound <> [] then
  failwith "reflected reciprocal jet: proof assumptions";;

let candle_q_dim_jet_inv_test_axioms_after = axioms ();;
if length candle_q_dim_jet_inv_test_axioms_after <>
     length candle_q_dim_jet_inv_test_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_q_dim_jet_inv_test_axioms_before)
       candle_q_dim_jet_inv_test_axioms_after) then
  failwith "reflected reciprocal jet: changed the global axiom set";;

let _ = print_endline
  "CANDLE_CV_ANALYTIC_DIM_JET_INV_RESULT dimensions=1 domains=2 accepted=1 rejected=1 semantic=1";;
let _ = print_endline "CANDLE_CV_ANALYTIC_DIM_JET_INV_OK";;
