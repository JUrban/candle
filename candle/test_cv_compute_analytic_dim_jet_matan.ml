(* ========================================================================== *)
(* Focused reflected crossing-zero [matan] dimension-jet regression.         *)
(* ========================================================================== *)

(* Loaded after [cv_compute_analytic_dim_jet_matan.ml] from the prepared
   action-296 checkpoint. *)

open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_dim_jet_matan;;

let candle_q_dim_jet_matan_test_axioms_before = axioms ();;

let candle_q_dim_jet_matan_test_input =
 `candle_q_dim_jet_make
    (((0,1),9),((1,0),9))
    [(((1,0),0),((1,0),0))]
    [[(((0,0),0),((0,0),0))]]`;;

let candle_q_dim_jet_matan_test_bad_input =
 `candle_q_dim_jet_make
    (((0,1),3),((1,0),9))
    [(((1,0),0),((1,0),0))]
    [[(((0,0),0),((0,0),0))]]`;;

let candle_q_dim_jet_matan_representation tm =
  REWRITE_CONV
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
    (mk_comb (`candle_cv_q_dim_jet_encode`,tm));;

let candle_q_dim_jet_matan_test_representation =
  candle_q_dim_jet_matan_representation candle_q_dim_jet_matan_test_input;;

let candle_q_dim_jet_matan_test_bad_representation =
  candle_q_dim_jet_matan_representation candle_q_dim_jet_matan_test_bad_input;;

let candle_q_dim_jet_matan_test_started = Unix.gettimeofday ();;

let candle_q_dim_jet_matan_test_computed =
  Kernel.compute
    (COMPUTE_INIT_THMS,candle_cv_q_dim_jet_matan_compute_eqs)
    (mk_comb
      (`candle_cv_q_dim_jet_matan`,
       rand (concl candle_q_dim_jet_matan_test_representation)));;

let candle_q_dim_jet_matan_domain_compute representation =
  Kernel.compute
    (COMPUTE_INIT_THMS,candle_cv_q_dim_jet_matan_compute_eqs)
    (mk_comb
      (`candle_cv_q_dim_jet_matan_domain`,
       rand (concl representation)));;

let candle_q_dim_jet_matan_test_domain_compute =
  candle_q_dim_jet_matan_domain_compute
    candle_q_dim_jet_matan_test_representation;;

let candle_q_dim_jet_matan_test_bad_domain_compute =
  candle_q_dim_jet_matan_domain_compute
    candle_q_dim_jet_matan_test_bad_representation;;

let candle_q_dim_jet_matan_test_result_link =
  TRANS
    (SYM
      (SPEC candle_q_dim_jet_matan_test_input
        candle_cv_q_dim_jet_matan_correct))
    (TRANS
      (AP_TERM `candle_cv_q_dim_jet_matan`
        candle_q_dim_jet_matan_test_representation)
      candle_q_dim_jet_matan_test_computed);;

let candle_q_dim_jet_matan_test_domain_link =
  TRANS
    (SYM
      (SPEC candle_q_dim_jet_matan_test_input
        candle_cv_q_dim_jet_matan_domain_correct))
    (TRANS
      (AP_TERM `candle_cv_q_dim_jet_matan_domain`
        candle_q_dim_jet_matan_test_representation)
      candle_q_dim_jet_matan_test_domain_compute);;

let candle_q_dim_jet_matan_bool_decision = prove
 (`!p. ((if p then 1 else 0) = 1) <=> p`,
  GEN_TAC THEN BOOL_CASES_TAC `p:bool` THEN REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_q_dim_jet_matan_test_domain =
  REWRITE_RULE
    [injectivity "cval"; candle_q_dim_jet_matan_bool_decision]
    candle_q_dim_jet_matan_test_domain_link;;

let candle_q_dim_jet_matan_test_shape = prove
 (`candle_q_dim_jet_shape 1
    (candle_q_dim_jet_make
      (((0,1),9),((1,0),9))
      [(((1,0),0),((1,0),0))]
      [[(((0,0),0),((0,0),0))]])`,
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_interval_matrix_shape_def;
              candle_q_dim_interval_rows_width_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; LENGTH; FST; SND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_q_dim_jet_matan_test_components = prove
 (`candle_q_dim_jet_contains_components 1
    (candle_q_dim_jet_make
      (((0,1),9),((1,0),9))
      [(((1,0),0),((1,0),0))]
      [[(((0,0),0),((0,0),0))]])
    (&0) (\i. &1) (\i j. &0)`,
  REWRITE_TAC[candle_q_dim_jet_contains_components_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_q_interval_contains_def; candle_q_real_def;
                candle_q_den_def; candle_lc_zreal_def; FST; SND] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
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
    CONV_TAC NUM_REDUCE_CONV THEN
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
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

let candle_q_dim_jet_matan_test_sound =
  MATCH_MP
    (SPECL
      [`1`; candle_q_dim_jet_matan_test_input; `&0:real`;
       `(\i. &1):num->real`; `(\i j. &0):num->num->real`]
      candle_q_dim_jet_matan_components_sound)
    (CONJ candle_q_dim_jet_matan_test_shape
      (CONJ candle_q_dim_jet_matan_test_domain
        candle_q_dim_jet_matan_test_components));;

let candle_q_dim_jet_matan_test_seconds =
  Unix.gettimeofday () -. candle_q_dim_jet_matan_test_started;;

if hyp candle_q_dim_jet_matan_test_computed <> [] ||
   hyp candle_q_dim_jet_matan_test_domain_compute <> [] ||
   hyp candle_q_dim_jet_matan_test_bad_domain_compute <> [] ||
   hyp candle_q_dim_jet_matan_test_result_link <> [] ||
   hyp candle_q_dim_jet_matan_test_domain <> [] ||
   hyp candle_q_dim_jet_matan_test_sound <> [] ||
   rand (concl candle_q_dim_jet_matan_test_domain_compute) <>
     `Cexp_num 1` ||
   rand (concl candle_q_dim_jet_matan_test_bad_domain_compute) <>
     `Cexp_num 0` then
  failwith "reflected matan dimension jet: theorem or domain mismatch";;

let candle_q_dim_jet_matan_test_axioms_after = axioms ();;
if length candle_q_dim_jet_matan_test_axioms_after <>
     length candle_q_dim_jet_matan_test_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_q_dim_jet_matan_test_axioms_before)
       candle_q_dim_jet_matan_test_axioms_after) then
  failwith "reflected matan dimension jet: changed the global axiom set";;

let _ =
  print_endline
    ("CANDLE_CV_ANALYTIC_DIM_JET_MATAN_RESULT dimension=1 valid=1 " ^
     "rejected=1 value_gradient_hessian=1 seconds=" ^
     string_of_float candle_q_dim_jet_matan_test_seconds);;

let _ = print_endline "CANDLE_CV_ANALYTIC_DIM_JET_MATAN_OK";;
