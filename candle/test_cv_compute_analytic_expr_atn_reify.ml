(* ========================================================================== *)
(* Source-authenticated reflected execution of pi/2 + atn x.                *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_reify.ml";;

open Candle_cv_linear_combination_core;;
open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_reify;;

let candle_analytic_expr_atn_reify_axioms_before = axioms ();;
let candle_analytic_expr_atn_reify_x = `x:real`;;
let candle_analytic_expr_atn_reify_source = `pi / &2 + atn x`;;

let candle_analytic_expr_atn_reify_no_sqrt _ =
  failwith "analytic atn reifier: unexpected square-root request";;

let candle_analytic_expr_atn_reified_ast,
    candle_analytic_expr_atn_reified_source =
  candle_analytic_reify_real_expression
    candle_analytic_expr_atn_reify_no_sqrt
    [candle_analytic_expr_atn_reify_x]
    candle_analytic_expr_atn_reify_source;;

let candle_analytic_expr_atn_reify_expanded_ast,
    candle_analytic_expr_atn_reify_expanded_source =
  candle_analytic_reify_real_expression
    candle_analytic_expr_atn_reify_no_sqrt
    [candle_analytic_expr_atn_reify_x]
    `pi * inv (&2) + atn x`;;

let candle_analytic_expr_atn_reify_expected_ast =
 `Candle_analytic_add Candle_analytic_pi_half
    (Candle_analytic_atn
      (Candle_analytic_poly (Candle_poly_var 0)))`;;

if not
    (aconv candle_analytic_expr_atn_reified_ast
      candle_analytic_expr_atn_reify_expected_ast) ||
   hyp candle_analytic_expr_atn_reified_source <> [] ||
   not
     (aconv (concl candle_analytic_expr_atn_reified_source)
       `candle_analytic_value [x]
          (Candle_analytic_add Candle_analytic_pi_half
            (Candle_analytic_atn
              (Candle_analytic_poly (Candle_poly_var 0)))) =
        pi / &2 + atn x`) then
  failwith "analytic atn reifier: authenticated source mismatch";;

if not
    (aconv candle_analytic_expr_atn_reify_expanded_ast
      candle_analytic_expr_atn_reify_expected_ast) ||
   hyp candle_analytic_expr_atn_reify_expanded_source <> [] ||
   not
     (aconv (concl candle_analytic_expr_atn_reify_expanded_source)
       `candle_analytic_value [x]
          (Candle_analytic_add Candle_analytic_pi_half
            (Candle_analytic_atn
              (Candle_analytic_poly (Candle_poly_var 0)))) =
        pi * inv (&2) + atn x`) then
  failwith "analytic atn reifier: expanded pi/2 source mismatch";;

let candle_analytic_expr_atn_reify_boxes =
 `([(((1,0),1),((1,0),1))]:
    (((num#num)#num)#((num#num)#num))list)`;;

let candle_analytic_expr_atn_reify_boxes_encoded =
  rand
    (concl
      (REWRITE_CONV
        [candle_cv_q_interval_list_def; candle_cv_q_interval_def;
         candle_cv_q_def; candle_cv_lc_z_def; FST; SND]
        (mk_comb (`candle_cv_q_interval_list`,
          candle_analytic_expr_atn_reify_boxes))));;

let candle_analytic_expr_atn_reify_program_encoded =
  rand
    (concl
      (REWRITE_CONV
        [candle_analytic_compile_def; candle_poly_compile_def; APPEND;
         candle_cv_analytic_instruction_list_def;
         candle_cv_analytic_instruction_def;
         candle_cv_q_instruction_list_def; candle_cv_q_instruction_def;
         FST; SND]
        (mk_comb (`candle_cv_analytic_instruction_list`,
          mk_comb (`candle_analytic_compile`,
            candle_analytic_expr_atn_reified_ast)))));;

let candle_analytic_expr_atn_reify_started = Unix.gettimeofday ();;

let candle_analytic_expr_atn_reify_result =
  Kernel.compute
    (COMPUTE_INIT_THMS,candle_cv_q_dim_analytic_program_compute_eqs)
    (list_mk_comb
      (`candle_cv_q_dim_analytic_program`,
       [candle_analytic_expr_atn_reify_boxes_encoded;
        candle_analytic_expr_atn_reify_program_encoded]));;

let candle_analytic_expr_atn_reify_representation =
  REWRITE_RULE
    [candle_cv_q_interval_list_def; candle_cv_q_interval_def;
     candle_cv_q_def; candle_cv_lc_z_def;
     candle_analytic_compile_def; candle_poly_compile_def; APPEND;
     candle_cv_analytic_instruction_list_def;
     candle_cv_analytic_instruction_def;
     candle_cv_q_instruction_list_def; candle_cv_q_instruction_def;
     FST; SND]
    (SPECL
      [candle_analytic_expr_atn_reified_ast;
       candle_analytic_expr_atn_reify_boxes]
      candle_cv_q_dim_analytic_compile_program_correct);;

let candle_analytic_expr_atn_reify_data =
  TRANS (SYM candle_analytic_expr_atn_reify_representation)
    candle_analytic_expr_atn_reify_result;;

let candle_analytic_expr_atn_reify_bool_decision = prove
 (`!p. ((if p then 1 else 0) = 1) <=> p`,
  GEN_TAC THEN BOOL_CASES_TAC `p:bool` THEN REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_analytic_expr_atn_reify_domain =
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
      candle_analytic_expr_atn_reify_data in
  REWRITE_RULE[candle_analytic_expr_atn_reify_bool_decision]
    (CONJUNCT1 result);;

let candle_analytic_expr_atn_reify_stack = prove
 (`candle_q_stack_contains
    [(((1,0),1),((1,0),1))] [&1 / &2]`,
  REWRITE_TAC[candle_q_stack_contains_def;
              candle_q_interval_contains_def; candle_q_real_def;
              candle_q_den_def; candle_lc_zreal_def; FST; SND] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let candle_analytic_expr_atn_reify_sound =
  MATCH_MP
    (SPECL
      [candle_analytic_expr_atn_reified_ast;
       candle_analytic_expr_atn_reify_boxes; `[&1 / &2]`]
      candle_q_dim_analytic_jet_sound)
    (CONJ candle_analytic_expr_atn_reify_stack
      candle_analytic_expr_atn_reify_domain);;

let candle_analytic_expr_atn_reify_seconds =
  Unix.gettimeofday () -. candle_analytic_expr_atn_reify_started;;

if hyp candle_analytic_expr_atn_reify_result <> [] ||
   hyp candle_analytic_expr_atn_reify_representation <> [] ||
   hyp candle_analytic_expr_atn_reify_domain <> [] ||
   hyp candle_analytic_expr_atn_reify_sound <> [] then
  failwith "analytic atn reifier: proof assumptions";;

let candle_analytic_expr_atn_reify_axioms_after = axioms ();;
if length candle_analytic_expr_atn_reify_axioms_after <>
     length candle_analytic_expr_atn_reify_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_analytic_expr_atn_reify_axioms_before)
       candle_analytic_expr_atn_reify_axioms_after) then
  failwith "analytic atn reifier: changed the global axiom set";;

let _ = print_endline
  ("CANDLE_CV_ANALYTIC_EXPR_ATN_REIFY_RESULT source=pi_half_plus_atn " ^
   "instructions=4 domain=1 semantic=1 seconds=" ^
   string_of_float candle_analytic_expr_atn_reify_seconds ^
   " output_md5=" ^
   Digest.to_hex
     (Digest.string (string_of_thm candle_analytic_expr_atn_reify_result)));;
let _ = print_endline "CANDLE_CV_ANALYTIC_EXPR_ATN_REIFY_OK";;
