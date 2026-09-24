(* ========================================================================== *)
(* Behavioral regression for analytic second-partial correspondence.        *)
(* ========================================================================== *)

load_path :=
  ["/project/worktrees/candle-cv-nonlinear-whole-box-v1"] @ !load_path;;

needs "candle/cv_compute_analytic_expr_hessian.ml";;

open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_derivatives;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_partials;;
open Candle_cv_analytic_expr_hessian;;

let candle_analytic_hessian_axioms_before = axioms ();;

let candle_analytic_hessian_fixture =
 `Candle_analytic_sqrt 2 0 0 2 0 0
    (Candle_analytic_add
      (Candle_analytic_inv
        (Candle_analytic_poly
          (Candle_poly_add
            (Candle_poly_const 1 0 0) (Candle_poly_var 0))))
      (Candle_analytic_poly (Candle_poly_const 3 0 0)))`;;

let candle_analytic_hessian_valid = prove
 (list_mk_comb
    (`candle_analytic_valid_dim`, [`1`;candle_analytic_hessian_fixture]),
  REWRITE_TAC[candle_analytic_valid_dim_def;
              candle_poly_valid_dim_def] THEN ARITH_TAC);;

let candle_analytic_hessian_regular = prove
 (list_mk_comb
    (`candle_analytic_regular_at`, [`[(&0)]`;candle_analytic_hessian_fixture]),
  REWRITE_TAC[candle_analytic_regular_at_def;
              candle_analytic_value_def; candle_poly_value_list_def;
              candle_q_real_def; candle_q_den_def; candle_lc_zreal_def;
              candle_q_real_lookup_def] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let candle_analytic_hessian_vec0_env = prove
 (`list_of_seq (\k. (vec 0:real^1)$(k + 1)) (dimindex (:1)) = [&0]`,
  REWRITE_TAC[DIMINDEX_1; num_CONV `1`; list_of_seq; APPEND;
              VEC_COMPONENT]);;

let candle_analytic_hessian_exact_dd = prove
 (mk_eq
    (list_mk_comb
      (`candle_analytic_dd`,
       [`0`;`0`;`[(&0)]`;candle_analytic_hessian_fixture]),
     `&15 / &32`),
  REWRITE_TAC[candle_analytic_dd_def; candle_analytic_d_def;
              candle_analytic_value_def; candle_poly_dd_list_def;
              candle_poly_d_list_def; candle_poly_value_list_def;
              candle_q_real_def; candle_q_den_def; candle_lc_zreal_def;
              candle_q_real_lookup_def] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SUBGOAL_THEN `sqrt (&4) = &2` SUBST1_TAC THENL
   [MATCH_MP_TAC SQRT_UNIQUE THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

let candle_analytic_hessian_index = prove
 (`1 IN 1..1`,
  REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC);;

let candle_analytic_hessian_instantiated =
  REWRITE_RULE[DIMINDEX_1; candle_analytic_hessian_vec0_env;
               ARITH_RULE `1 - 1 = 0`]
    (ISPECL
      [candle_analytic_hessian_fixture; `vec 0:real^1`; `1`; `1`]
      candle_analytic_denote_dim_second_partial);;

let candle_analytic_hessian_theorem =
  MATCH_MP candle_analytic_hessian_instantiated
    (CONJ candle_analytic_hessian_valid
      (CONJ candle_analytic_hessian_regular
        candle_analytic_hessian_index));;

let candle_analytic_hessian_exact =
  TRANS candle_analytic_hessian_theorem candle_analytic_hessian_exact_dd;;

if hyp candle_analytic_hessian_exact <> [] then
  failwith "analytic Hessian bridge: theorem assumptions";;

let candle_analytic_hessian_axioms_after = axioms ();;
if length candle_analytic_hessian_axioms_after <>
     length candle_analytic_hessian_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_analytic_hessian_axioms_before)
       candle_analytic_hessian_axioms_after) then
  failwith "analytic Hessian bridge: changed the global axiom set";;

let _ = print_endline
  "CANDLE_CV_ANALYTIC_EXPR_HESSIAN_RESULT constructors=7 second_partial=15/32";;
let _ = print_endline "CANDLE_CV_ANALYTIC_EXPR_HESSIAN_OK";;
