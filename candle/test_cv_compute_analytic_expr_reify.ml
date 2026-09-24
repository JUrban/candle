(* ========================================================================== *)
(* Source-to-reflected-program regression for nested analytic expressions.   *)
(* ========================================================================== *)

load_path :=
  ["/project/worktrees/candle-cv-nonlinear-whole-box-v1"] @ !load_path;;

needs "candle/cv_compute_analytic_expr_reify.ml";;

open Candle_cv_linear_combination_core;;
open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_reify;;

let candle_analytic_expr_reify_axioms_before = axioms ();;

let candle_analytic_expr_reify_x = `x:real`;;
let candle_analytic_expr_reify_source =
 `sqrt (inv (&1 + x) + &3)`;;

let candle_analytic_expr_reify_sqrt_interval tm =
  if not (aconv tm candle_analytic_expr_reify_source) then
    failwith "analytic source reifier: unexpected square-root request";
  `((((2,0),0),((2,0),0)):
      ((num#num)#num)#((num#num)#num))`;;

let candle_analytic_expr_reified_ast,
    candle_analytic_expr_reified_source =
  candle_analytic_reify_real_expression
    candle_analytic_expr_reify_sqrt_interval
    [candle_analytic_expr_reify_x]
    candle_analytic_expr_reify_source;;

let candle_analytic_expr_reify_expected_ast =
 `Candle_analytic_sqrt 2 0 0 2 0 0
    (Candle_analytic_add
      (Candle_analytic_inv
        (Candle_analytic_poly
          (Candle_poly_add
            (Candle_poly_const 1 0 0) (Candle_poly_var 0))))
      (Candle_analytic_poly (Candle_poly_const 3 0 0)))`;;

if not (aconv candle_analytic_expr_reified_ast
               candle_analytic_expr_reify_expected_ast) ||
   hyp candle_analytic_expr_reified_source <> [] ||
   not
     (aconv (concl candle_analytic_expr_reified_source)
       `candle_analytic_value [x]
          (Candle_analytic_sqrt 2 0 0 2 0 0
            (Candle_analytic_add
              (Candle_analytic_inv
                (Candle_analytic_poly
                  (Candle_poly_add
                    (Candle_poly_const 1 0 0) (Candle_poly_var 0))))
              (Candle_analytic_poly (Candle_poly_const 3 0 0)))) =
        sqrt (inv (&1 + x) + &3)`) then
  failwith "analytic source reifier: authenticated AST mismatch";;

let candle_analytic_expr_reify_boxes =
 `[(((((0,0),0),((0,0),0))):
      ((num#num)#num)#((num#num)#num))]`;;

let candle_analytic_expr_reify_expected_jet =
 `candle_q_dim_jet_make
    (((2,0),0),((2,0),0))
    [(((0,1),3),((0,1),3))]
    [[(((15,0),31),((15,0),31))]]`;;

let candle_analytic_expr_reify_boxes_encoded =
  rand
    (concl
      (REWRITE_CONV
        [candle_cv_q_interval_list_def; candle_cv_q_interval_def;
         candle_cv_q_def; candle_cv_lc_z_def; FST; SND]
        (mk_comb (`candle_cv_q_interval_list`,
          candle_analytic_expr_reify_boxes))));;

let candle_analytic_expr_reify_program_encoded =
  rand
    (concl
      (REWRITE_CONV
        [candle_analytic_compile_def; candle_poly_compile_def; APPEND;
         candle_cv_analytic_instruction_list_def;
         candle_cv_analytic_instruction_def;
         candle_cv_q_instruction_list_def; candle_cv_q_instruction_def;
         candle_analytic_sqrt_interval_def;
         candle_cv_q_interval_def; candle_cv_q_def; candle_cv_lc_z_def;
         FST; SND]
        (mk_comb (`candle_cv_analytic_instruction_list`,
          mk_comb (`candle_analytic_compile`,
            candle_analytic_expr_reified_ast)))));;

let candle_analytic_expr_reify_expected =
  rand
    (concl
      (REWRITE_CONV
        [candle_cv_q_dim_analytic_result_encode_def;
         candle_cv_q_dim_analytic_result_make_def; candle_cv_bool_def;
         candle_cv_q_dim_jet_encode_def; candle_cv_q_dim_jet_make_def;
         candle_cv_q_interval_matrix_def; candle_cv_q_interval_list_def;
         candle_cv_q_interval_def; candle_cv_q_def; candle_cv_lc_z_def;
         candle_q_dim_jet_make_def; candle_q_dim_jet_f_def;
         candle_q_dim_jet_gradient_def; candle_q_dim_jet_hessian_def;
         ARITH_RULE `SUC 0 = 1`; FST; SND]
        (mk_comb (`candle_cv_q_dim_analytic_result_encode`,
          mk_pair (`T`,candle_analytic_expr_reify_expected_jet)))));;

let candle_analytic_expr_reify_computed =
  Kernel.compute
    (COMPUTE_INIT_THMS,candle_cv_q_dim_analytic_program_compute_eqs)
    (list_mk_comb
      (`candle_cv_q_dim_analytic_program`,
       [candle_analytic_expr_reify_boxes_encoded;
        candle_analytic_expr_reify_program_encoded]));;

if not
    (aconv (rand (concl candle_analytic_expr_reify_computed))
      candle_analytic_expr_reify_expected) then
  failwith "analytic source reifier: reflected result mismatch";;

let candle_analytic_expr_reify_representation =
  REWRITE_RULE
    [candle_cv_q_interval_list_def; candle_cv_q_interval_def;
     candle_cv_q_def; candle_cv_lc_z_def;
     candle_analytic_compile_def; candle_poly_compile_def; APPEND;
     candle_cv_analytic_instruction_list_def;
     candle_cv_analytic_instruction_def;
     candle_cv_q_instruction_list_def; candle_cv_q_instruction_def;
     candle_analytic_sqrt_interval_def; FST; SND]
    (SPECL
      [candle_analytic_expr_reified_ast;
       candle_analytic_expr_reify_boxes]
      candle_cv_q_dim_analytic_compile_program_correct);;

let candle_analytic_expr_reify_data =
  TRANS (SYM candle_analytic_expr_reify_representation)
    candle_analytic_expr_reify_computed;;

let candle_analytic_expr_reify_bool_decision = prove
 (`!p. ((if p then 1 else 0) = 1) <=> p`,
  GEN_TAC THEN BOOL_CASES_TAC `p:bool` THEN REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_analytic_expr_reify_domain =
  let result =
    REWRITE_RULE
      [candle_cv_q_dim_analytic_result_encode_def;
       candle_cv_q_dim_analytic_result_make_def; candle_cv_bool_def;
       candle_cv_q_dim_jet_encode_def; candle_cv_q_dim_jet_make_def;
       candle_cv_q_interval_matrix_def; candle_cv_q_interval_list_def;
       candle_cv_q_interval_def; candle_cv_q_def; candle_cv_lc_z_def;
       candle_q_dim_jet_make_def; candle_q_dim_jet_f_def;
       candle_q_dim_jet_gradient_def; candle_q_dim_jet_hessian_def;
       ARITH_RULE `SUC 0 = 1`; injectivity "cval"; FST; SND]
      candle_analytic_expr_reify_data in
  REWRITE_RULE[candle_analytic_expr_reify_bool_decision]
    (CONJUNCT1 result);;

if hyp candle_analytic_expr_reify_computed <> [] ||
   hyp candle_analytic_expr_reify_representation <> [] ||
   hyp candle_analytic_expr_reify_domain <> [] then
  failwith "analytic source reifier: proof assumptions";;

let candle_analytic_expr_reify_axioms_after = axioms ();;
if length candle_analytic_expr_reify_axioms_after <>
     length candle_analytic_expr_reify_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_analytic_expr_reify_axioms_before)
       candle_analytic_expr_reify_axioms_after) then
  failwith "analytic source reifier: changed the global axiom set";;

let _ = print_endline
  "CANDLE_CV_ANALYTIC_EXPR_REIFY_RESULT source_nodes=8 analytic_instructions=5 domain=1 value=2 gradient=-1/4 hessian=15/32 correspondence=1";;
let _ = print_endline "CANDLE_CV_ANALYTIC_EXPR_REIFY_OK";;
