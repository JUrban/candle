(* ========================================================================== *)
(* Focused source-to-shared-jet reciprocal integration regression.           *)
(* ========================================================================== *)

load_path :=
  ["/project/worktrees/candle-cv-nonlinear-whole-box-v1"] @ !load_path;;

needs "candle/cv_compute_analytic_poly_inv.ml";;

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
open Candle_cv_analytic_poly_inv;;

let candle_analytic_poly_inv_axioms_before = axioms ();;

let candle_analytic_poly_inv_variables = [`x:real`];;
let candle_analytic_poly_inv_source = `inv (&2 + x)`;;

let candle_analytic_poly_inv_ast,
    candle_analytic_poly_inv_valid,
    candle_analytic_poly_inv_source_th,
    candle_analytic_poly_inv_program,
    candle_analytic_poly_inv_run_th =
  candle_poly_inv_reify_real_expression
    candle_analytic_poly_inv_variables candle_analytic_poly_inv_source;;

let candle_analytic_poly_inv_expected_ast =
  `Candle_poly_add (Candle_poly_const 2 0 0) (Candle_poly_var 0)`;;

if not
    (aconv candle_analytic_poly_inv_ast
      candle_analytic_poly_inv_expected_ast) ||
   hyp candle_analytic_poly_inv_valid <> [] ||
   hyp candle_analytic_poly_inv_source_th <> [] ||
   hyp candle_analytic_poly_inv_run_th <> [] ||
   length (dest_list candle_analytic_poly_inv_program) <> 3 then
  failwith "analytic reciprocal: source reification mismatch";;

let candle_analytic_poly_inv_boxes =
  `[(((((0,0),0),((0,0),0))):
       ((num#num)#num)#((num#num)#num))]`;;

let candle_analytic_poly_inv_expected =
 `candle_q_dim_jet_make
    (((1,0),1),((1,0),1))
    [(((0,1),3),((0,1),3))]
    [[(((1,0),3),((1,0),3))]]`;;

let candle_analytic_poly_inv_program_rep =
  REWRITE_CONV
    [candle_cv_q_instruction_list_def; candle_cv_q_instruction_def;
     candle_cv_q_def; candle_cv_lc_z_def]
    (mk_comb
      (`candle_cv_q_instruction_list`,candle_analytic_poly_inv_program));;

let candle_analytic_poly_inv_boxes_rep =
  REWRITE_CONV
    [candle_cv_q_interval_list_def; candle_cv_q_interval_def;
     candle_cv_q_def; candle_cv_lc_z_def]
    (mk_comb
      (`candle_cv_q_interval_list`,candle_analytic_poly_inv_boxes));;

let candle_analytic_poly_inv_jet_encode tm =
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

let candle_analytic_poly_inv_program_rep_tm =
  rand (concl candle_analytic_poly_inv_program_rep);;
let candle_analytic_poly_inv_boxes_rep_tm =
  rand (concl candle_analytic_poly_inv_boxes_rep);;

let candle_analytic_poly_inv_computed =
  Kernel.compute
    (COMPUTE_INIT_THMS,candle_cv_q_dim_poly_inv_compute_eqs)
    (list_mk_comb
      (`candle_cv_q_dim_poly_inv_program`,
       [candle_analytic_poly_inv_boxes_rep_tm;
        candle_analytic_poly_inv_program_rep_tm]));;

let candle_analytic_poly_inv_computed_domain =
  Kernel.compute
    (COMPUTE_INIT_THMS,candle_cv_q_dim_poly_inv_compute_eqs)
    (list_mk_comb
      (`candle_cv_q_dim_poly_inv_domain`,
       [candle_analytic_poly_inv_boxes_rep_tm;
        candle_analytic_poly_inv_program_rep_tm]));;

if not
    (aconv (rand (concl candle_analytic_poly_inv_computed))
      (candle_analytic_poly_inv_jet_encode
        candle_analytic_poly_inv_expected)) ||
   not (aconv (rand (concl candle_analytic_poly_inv_computed_domain))
          `Cexp_num 1`) then
  failwith "analytic reciprocal: computed shared jet mismatch";;

let candle_analytic_poly_inv_domain_correct =
  PURE_REWRITE_RULE
    [candle_analytic_poly_inv_boxes_rep;
     candle_analytic_poly_inv_program_rep]
    (SPECL
      [candle_analytic_poly_inv_boxes;
       candle_analytic_poly_inv_program]
      candle_cv_q_dim_poly_inv_domain_correct);;

let candle_analytic_poly_inv_domain_flag =
  TRANS (SYM candle_analytic_poly_inv_computed_domain)
    candle_analytic_poly_inv_domain_correct;;

let candle_analytic_poly_inv_domain_tm =
  list_mk_comb
    (`candle_q_dim_poly_inv_domain`,
     [candle_analytic_poly_inv_boxes;
      candle_analytic_poly_inv_program]);;

let candle_analytic_poly_inv_domain_num_flag =
  REWRITE_RULE[injectivity "cval"]
    candle_analytic_poly_inv_domain_flag;;

let candle_analytic_poly_inv_flag_accept = prove
 (`!b. (1:num) = (if b then 1 else 0) ==> b`,
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_analytic_poly_inv_domain =
  MATCH_MP
    (SPEC candle_analytic_poly_inv_domain_tm
      candle_analytic_poly_inv_flag_accept)
    candle_analytic_poly_inv_domain_num_flag;;

let candle_analytic_poly_inv_stack_tm =
  let env = `[candle_q_real ((0,0),0)]` in
  list_mk_comb
    (`candle_q_stack_contains`,
     [candle_analytic_poly_inv_boxes; env]);;

let candle_analytic_poly_inv_stack = prove
 (candle_analytic_poly_inv_stack_tm,
  REWRITE_TAC[candle_q_stack_contains_def;
              candle_q_exact_interval_contains]);;

let candle_analytic_poly_inv_compile =
  REWRITE_CONV[candle_poly_compile_def; APPEND]
    (mk_comb (`candle_poly_compile`,candle_analytic_poly_inv_ast));;

if not
    (aconv (rand (concl candle_analytic_poly_inv_compile))
      candle_analytic_poly_inv_program) then
  failwith "analytic reciprocal: compiled program mismatch";;

let candle_analytic_poly_inv_sound =
  MATCH_MP
    (PURE_REWRITE_RULE[candle_analytic_poly_inv_compile]
      (SPECL
        [candle_analytic_poly_inv_ast;
         candle_analytic_poly_inv_boxes;
         `[candle_q_real ((0,0),0)]`]
        candle_q_dim_poly_inv_program_sound))
    (CONJ candle_analytic_poly_inv_stack
      candle_analytic_poly_inv_domain);;

if hyp candle_analytic_poly_inv_computed <> [] ||
   hyp candle_analytic_poly_inv_computed_domain <> [] ||
   hyp candle_analytic_poly_inv_domain <> [] ||
   hyp candle_analytic_poly_inv_stack <> [] ||
   hyp candle_analytic_poly_inv_sound <> [] then
  failwith "analytic reciprocal: proof assumptions";;

let candle_analytic_poly_inv_axioms_after = axioms ();;
if length candle_analytic_poly_inv_axioms_after <>
     length candle_analytic_poly_inv_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_analytic_poly_inv_axioms_before)
       candle_analytic_poly_inv_axioms_after) then
  failwith "analytic reciprocal: changed the global axiom set";;

let _ = print_endline
  "CANDLE_CV_ANALYTIC_POLY_INV_RESULT sources=1 instructions=3 dimensions=1 domains=1 accepted=1 semantic=1";;
let _ = print_endline "CANDLE_CV_ANALYTIC_POLY_INV_OK";;
