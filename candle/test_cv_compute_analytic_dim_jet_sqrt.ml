(* ========================================================================== *)
(* Focused reflected dimension-generic square-root-jet regression.           *)
(* ========================================================================== *)

load_path :=
  ["/project/worktrees/candle-cv-nonlinear-whole-box-v1"] @ !load_path;;

needs "candle/cv_compute_analytic_dim_jet_sqrt.ml";;

open Candle_cv_linear_combination_core;;
open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_exact_interval_inv_core;;
open Candle_cv_exact_interval_sqrt_certificate;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_dim_jet_inv;;
open Candle_cv_analytic_dim_jet_sqrt;;

let candle_q_dim_jet_sqrt_test_axioms_before = axioms ();;

let candle_q_dim_jet_sqrt_test_input =
 `candle_q_dim_jet_make
    (((4,0),0),((4,0),0))
    [(((1,0),0),((1,0),0))]
    [[(((0,0),0),((0,0),0))]]`;;

let candle_q_dim_jet_sqrt_test_input_expanded =
  rand
    (concl
      (REWRITE_CONV[candle_q_dim_jet_make_def]
        candle_q_dim_jet_sqrt_test_input));;

let candle_q_dim_jet_sqrt_test_output =
 `((((2,0),0),((2,0),0)):
    ((num#num)#num)#((num#num)#num))`;;

let candle_q_dim_jet_sqrt_test_bad_output =
 `((((3,0),0),((3,0),0)):
    ((num#num)#num)#((num#num)#num))`;;

let candle_q_dim_jet_sqrt_test_zero_input =
 `candle_q_dim_jet_make
    (((0,0),0),((0,0),0))
    [(((1,0),0),((1,0),0))]
    [[(((0,0),0),((0,0),0))]]`;;

let candle_q_dim_jet_sqrt_test_zero_output =
 `((((0,0),0),((0,0),0)):
    ((num#num)#num)#((num#num)#num))`;;

let candle_q_dim_jet_sqrt_test_expected =
 `candle_q_dim_jet_make
    (((2,0),0),((2,0),0))
    [(((1,0),3),((1,0),3))]
    [[(((0,1),31),((0,1),31))]]`;;

let candle_q_dim_jet_sqrt_encode tm =
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

let candle_q_dim_jet_sqrt_interval_encode tm =
  rand
    (concl
      (REWRITE_CONV
        [candle_cv_q_interval_def; candle_cv_q_def;
         candle_cv_lc_z_def; FST; SND]
        (mk_comb (`candle_cv_q_interval`,tm))));;

let candle_q_dim_jet_sqrt_test_computed =
  Kernel.compute
    (COMPUTE_INIT_THMS,candle_cv_q_dim_jet_sqrt_compute_eqs)
    (list_mk_comb
      (`candle_cv_q_dim_jet_sqrt_with`,
       [candle_q_dim_jet_sqrt_interval_encode
          candle_q_dim_jet_sqrt_test_output;
        candle_q_dim_jet_sqrt_encode candle_q_dim_jet_sqrt_test_input]));;

let candle_q_dim_jet_sqrt_domain_compute s a =
  Kernel.compute
    (COMPUTE_INIT_THMS,candle_cv_q_dim_jet_sqrt_compute_eqs)
    (list_mk_comb
      (`candle_cv_q_dim_jet_sqrt_domain`,
       [candle_q_dim_jet_sqrt_interval_encode s;
        candle_q_dim_jet_sqrt_encode a]));;

let candle_q_dim_jet_sqrt_test_domain =
  candle_q_dim_jet_sqrt_domain_compute
    candle_q_dim_jet_sqrt_test_output candle_q_dim_jet_sqrt_test_input;;

let candle_q_dim_jet_sqrt_test_bad_domain =
  candle_q_dim_jet_sqrt_domain_compute
    candle_q_dim_jet_sqrt_test_bad_output candle_q_dim_jet_sqrt_test_input;;

let candle_q_dim_jet_sqrt_test_zero_domain =
  candle_q_dim_jet_sqrt_domain_compute
    candle_q_dim_jet_sqrt_test_zero_output
    candle_q_dim_jet_sqrt_test_zero_input;;

if not
    (aconv (rand (concl candle_q_dim_jet_sqrt_test_computed))
      (candle_q_dim_jet_sqrt_encode candle_q_dim_jet_sqrt_test_expected)) ||
   not (aconv (rand (concl candle_q_dim_jet_sqrt_test_domain))
          `Cexp_num 1`) ||
   not (aconv (rand (concl candle_q_dim_jet_sqrt_test_bad_domain))
          `Cexp_num 0`) ||
   not (aconv (rand (concl candle_q_dim_jet_sqrt_test_zero_domain))
          `Cexp_num 0`) then
  failwith "reflected square-root jet: computed result mismatch";;

let candle_q_dim_jet_sqrt_test_domain_correct =
  REWRITE_RULE
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
    (SPECL
      [candle_q_dim_jet_sqrt_test_output;
       candle_q_dim_jet_sqrt_test_input]
      candle_cv_q_dim_jet_sqrt_domain_correct);;

let candle_q_dim_jet_sqrt_test_domain_decision =
  TRANS (SYM candle_q_dim_jet_sqrt_test_domain_correct)
    candle_q_dim_jet_sqrt_test_domain;;

let candle_q_dim_jet_sqrt_bool_decision = prove
 (`!p. ((if p then 1 else 0) = 1) <=> p`,
  GEN_TAC THEN BOOL_CASES_TAC `p:bool` THEN REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_q_dim_jet_sqrt_test_input_domain =
  REWRITE_RULE
    [injectivity "cval"; candle_q_dim_jet_sqrt_bool_decision]
    candle_q_dim_jet_sqrt_test_domain_decision;;

let candle_q_dim_jet_sqrt_test_input_shape = prove
 (`candle_q_dim_jet_shape 1
    (candle_q_dim_jet_make
      (((4,0),0),((4,0),0))
      [(((1,0),0),((1,0),0))]
      [[(((0,0),0),((0,0),0))]])`,
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_interval_matrix_shape_def;
              candle_q_dim_interval_rows_width_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; LENGTH; FST; SND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_q_dim_jet_sqrt_test_input_components = prove
 (`candle_q_dim_jet_contains_components 1
    (candle_q_dim_jet_make
      (((4,0),0),((4,0),0))
      [(((1,0),0),((1,0),0))]
      [[(((0,0),0),((0,0),0))]])
    (&4) (\i. &1) (\i j. &0)`,
  REWRITE_TAC[candle_q_dim_jet_contains_components_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_q_interval_contains_def; candle_q_real_def;
                candle_q_den_def; candle_lc_zreal_def; FST; SND] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
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
    CONV_TAC REAL_RAT_REDUCE_CONV;
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
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

let candle_q_dim_jet_sqrt_test_input_shape_expanded =
  REWRITE_RULE[candle_q_dim_jet_make_def]
    candle_q_dim_jet_sqrt_test_input_shape;;

let candle_q_dim_jet_sqrt_test_input_components_expanded =
  REWRITE_RULE[candle_q_dim_jet_make_def]
    candle_q_dim_jet_sqrt_test_input_components;;

let candle_q_dim_jet_sqrt_test_sound =
  MATCH_MP
    (SPECL
      [`1`; candle_q_dim_jet_sqrt_test_output;
       candle_q_dim_jet_sqrt_test_input_expanded; `&4:real`;
       `(\i. &1):num->real`; `(\i j. &0):num->num->real`]
      candle_q_dim_jet_sqrt_components_sound)
    (CONJ candle_q_dim_jet_sqrt_test_input_shape_expanded
      (CONJ candle_q_dim_jet_sqrt_test_input_domain
        candle_q_dim_jet_sqrt_test_input_components_expanded));;

if hyp candle_q_dim_jet_sqrt_test_computed <> [] ||
   hyp candle_q_dim_jet_sqrt_test_domain <> [] ||
   hyp candle_q_dim_jet_sqrt_test_bad_domain <> [] ||
   hyp candle_q_dim_jet_sqrt_test_zero_domain <> [] ||
   hyp candle_q_dim_jet_sqrt_test_sound <> [] then
  failwith "reflected square-root jet: proof assumptions";;

let candle_q_dim_jet_sqrt_test_axioms_after = axioms ();;
if length candle_q_dim_jet_sqrt_test_axioms_after <>
     length candle_q_dim_jet_sqrt_test_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_q_dim_jet_sqrt_test_axioms_before)
       candle_q_dim_jet_sqrt_test_axioms_after) then
  failwith "reflected square-root jet: changed the global axiom set";;

let _ = print_endline
  "CANDLE_CV_ANALYTIC_DIM_JET_SQRT_RESULT dimensions=1 domains=3 accepted=1 rejected=2 semantic=1";;
let _ = print_endline "CANDLE_CV_ANALYTIC_DIM_JET_SQRT_OK";;
