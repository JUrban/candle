(* ========================================================================== *)
(* Proof-producing symbolic differentiation for reflected polynomials.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This provides an immediately executable       *)
(* dimension-parametric route through the existing reflected interval-program *)
(* evaluator: compile the source AST and its mechanically generated first and *)
(* second derivative ASTs, then check all numerical enclosures as data.       *)
(* ========================================================================== *)

needs "candle/cv_compute_polynomial_expr_dim_calculus.ml";;
needs "candle/cv_compute_whole_box_dim_taylor.ml";;

module Candle_cv_polynomial_expr_diff = struct

open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_whole_box_jet;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_derivatives;;
open Candle_cv_polynomial_expr_dim_calculus;;

let candle_poly_diff_def = define
 `(candle_poly_diff di (Candle_poly_const p n d) =
     Candle_poly_const 0 0 0) /\
  (candle_poly_diff di (Candle_poly_var i) =
     if i = di then Candle_poly_const 1 0 0
     else Candle_poly_const 0 0 0) /\
  (candle_poly_diff di (Candle_poly_neg a) =
     Candle_poly_neg (candle_poly_diff di a)) /\
  (candle_poly_diff di (Candle_poly_add a b) =
     Candle_poly_add (candle_poly_diff di a) (candle_poly_diff di b)) /\
  (candle_poly_diff di (Candle_poly_mul a b) =
     Candle_poly_add
       (Candle_poly_mul (candle_poly_diff di a) b)
       (Candle_poly_mul a (candle_poly_diff di b))) /\
  (candle_poly_diff di (Candle_poly_square a) =
     Candle_poly_add
       (Candle_poly_mul (candle_poly_diff di a) a)
       (Candle_poly_mul a (candle_poly_diff di a)))`;;

let candle_poly_diff2_def = new_definition
 `candle_poly_diff2 dj di e =
    candle_poly_diff dj (candle_poly_diff di e)`;;

let candle_poly_zero_real = prove
 (`candle_q_real (((0,0),0):(num#num)#num) = &0`,
  REWRITE_TAC[candle_q_real_def; candle_q_den_def; candle_lc_zreal_def;
              FST; SND; real_div; REAL_SUB_REFL; REAL_MUL_LZERO]);;

let candle_poly_one_real = prove
 (`candle_q_real (((1,0),0):(num#num)#num) = &1`,
  REWRITE_TAC[GSYM candle_q_one_def; candle_q_real_one]);;

let candle_poly_diff_valid = prove
 (`!e nvars di.
     candle_poly_valid_dim nvars e
     ==> candle_poly_valid_dim nvars (candle_poly_diff di e)`,
  MATCH_MP_TAC candle_poly_expr_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[candle_poly_diff_def; candle_poly_valid_dim_def] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[candle_poly_valid_dim_def]) THEN
  ASM_MESON_TAC[]);;

let candle_poly_diff2_valid = prove
 (`!e nvars di dj.
     candle_poly_valid_dim nvars e
     ==> candle_poly_valid_dim nvars (candle_poly_diff2 dj di e)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_poly_diff2_def] THEN
  MATCH_MP_TAC
   (SPECL
     [`candle_poly_diff di e`; `nvars:num`; `dj:num`]
     candle_poly_diff_valid) THEN
  MATCH_MP_TAC
   (SPECL [`e:candle_poly_expr`; `nvars:num`; `di:num`]
     candle_poly_diff_valid) THEN
  ASM_REWRITE_TAC[]);;

let candle_poly_diff_value_fun = prove
 (`!e rho di.
     candle_poly_value_fun rho (candle_poly_diff di e) =
     candle_poly_d_fun di rho e`,
  MATCH_MP_TAC candle_poly_expr_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[candle_poly_diff_def; candle_poly_value_fun_def;
                  candle_poly_d_fun_def; candle_poly_zero_real;
                  candle_poly_one_real] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[candle_poly_value_fun_def;
                                             candle_poly_zero_real;
                                             candle_poly_one_real]) THEN
  CONV_TAC REAL_RING);;

let candle_poly_diff_d_fun = prove
 (`!e rho di dj.
     candle_poly_d_fun dj rho (candle_poly_diff di e) =
     candle_poly_dd_fun dj di rho e`,
  MATCH_MP_TAC candle_poly_expr_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[candle_poly_diff_def; candle_poly_value_fun_def;
                  candle_poly_d_fun_def; candle_poly_dd_fun_def;
                  candle_poly_diff_value_fun; candle_poly_zero_real;
                  candle_poly_one_real] THEN
  REPEAT(COND_CASES_TAC THEN
    ASM_REWRITE_TAC[candle_poly_value_fun_def; candle_poly_d_fun_def;
                    candle_poly_zero_real; candle_poly_one_real]) THEN
  CONV_TAC REAL_RING);;

let candle_poly_diff2_value_fun = prove
 (`!e rho di dj.
     candle_poly_value_fun rho (candle_poly_diff2 dj di e) =
     candle_poly_dd_fun dj di rho e`,
  REWRITE_TAC[candle_poly_diff2_def; candle_poly_diff_value_fun;
              candle_poly_diff_d_fun]);;

(* Equivalent finite-list statements are the executable compiler boundary. *)

let candle_poly_diff_value_list = prove
 (`!e env di.
     candle_poly_value_list env (candle_poly_diff di e) =
     candle_poly_d_list di env e`,
  MATCH_MP_TAC candle_poly_expr_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[candle_poly_diff_def; candle_poly_value_list_def;
                  candle_poly_d_list_def; candle_poly_zero_real;
                  candle_poly_one_real] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[candle_poly_value_list_def;
                                             candle_poly_zero_real;
                                             candle_poly_one_real]) THEN
  CONV_TAC REAL_RING);;

let candle_poly_diff_d_list = prove
 (`!e env di dj.
     candle_poly_d_list dj env (candle_poly_diff di e) =
     candle_poly_dd_list dj di env e`,
  MATCH_MP_TAC candle_poly_expr_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[candle_poly_diff_def; candle_poly_value_list_def;
                  candle_poly_d_list_def; candle_poly_dd_list_def;
                  candle_poly_diff_value_list; candle_poly_zero_real;
                  candle_poly_one_real] THEN
  REPEAT(COND_CASES_TAC THEN
    ASM_REWRITE_TAC[candle_poly_value_list_def; candle_poly_d_list_def;
                    candle_poly_zero_real; candle_poly_one_real]) THEN
  CONV_TAC REAL_RING);;

let candle_poly_diff2_value_list = prove
 (`!e env di dj.
     candle_poly_value_list env (candle_poly_diff2 dj di e) =
     candle_poly_dd_list dj di env e`,
  REWRITE_TAC[candle_poly_diff2_def; candle_poly_diff_value_list;
              candle_poly_diff_d_list]);;

let candle_poly_diff_compile_real_program = prove
 (`!e env di.
     candle_q_real_run env
       (candle_poly_compile (candle_poly_diff di e)) [] =
     [candle_poly_d_list di env e]`,
  REWRITE_TAC[candle_poly_compile_real_program;
              candle_poly_diff_value_list]);;

let candle_poly_diff2_compile_real_program = prove
 (`!e env di dj.
     candle_q_real_run env
       (candle_poly_compile (candle_poly_diff2 dj di e)) [] =
     [candle_poly_dd_list dj di env e]`,
  REWRITE_TAC[candle_poly_compile_real_program;
              candle_poly_diff2_value_list]);;

(* The dimension-generic checker must not accept an unrelated gradient or    *)
(* Hessian program as an extra source of authority.  Derive every component  *)
(* program inside HOL from the authenticated expression AST.                 *)

let candle_poly_gradient_programs_def = new_definition
 `candle_poly_gradient_programs nvars e =
    list_of_seq
      (\di. candle_poly_compile (candle_poly_diff di e)) nvars`;;

let candle_poly_hessian_programs_def = new_definition
 `candle_poly_hessian_programs nvars e =
    list_of_seq
      (\di. list_of_seq
        (\dj. candle_poly_compile (candle_poly_diff2 dj di e)) nvars)
      nvars`;;

let candle_poly_gradient_programs_length = prove
 (`!nvars e. LENGTH (candle_poly_gradient_programs nvars e) = nvars`,
  REWRITE_TAC[candle_poly_gradient_programs_def; LENGTH_LIST_OF_SEQ]);;

let candle_poly_gradient_programs_el = prove
 (`!nvars e di.
     di < nvars
     ==> EL di (candle_poly_gradient_programs nvars e) =
         candle_poly_compile (candle_poly_diff di e)`,
  SIMP_TAC[candle_poly_gradient_programs_def; EL_LIST_OF_SEQ]);;

let candle_poly_hessian_programs_length = prove
 (`!nvars e. LENGTH (candle_poly_hessian_programs nvars e) = nvars`,
  REWRITE_TAC[candle_poly_hessian_programs_def; LENGTH_LIST_OF_SEQ]);;

let candle_poly_hessian_programs_row_length = prove
 (`!nvars e di.
     di < nvars
     ==> LENGTH (EL di (candle_poly_hessian_programs nvars e)) = nvars`,
  SIMP_TAC[candle_poly_hessian_programs_def; EL_LIST_OF_SEQ;
           LENGTH_LIST_OF_SEQ]);;

let candle_poly_hessian_programs_el = prove
 (`!nvars e di dj.
     di < nvars /\ dj < nvars
     ==> EL dj (EL di (candle_poly_hessian_programs nvars e)) =
         candle_poly_compile (candle_poly_diff2 dj di e)`,
  SIMP_TAC[candle_poly_hessian_programs_def; EL_LIST_OF_SEQ]);;

(* The existing reflected interval evaluator can therefore enclose each      *)
(* generated component with no expression-specific arithmetic proof.         *)

let candle_poly_interval_sound = prove
 (`!e ienv env.
     candle_q_stack_contains ienv env
     ==> candle_q_interval_contains
          (candle_q_program_interval ienv (candle_poly_compile e))
          (candle_poly_value_list env e)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_q_program_interval_def] THEN
  MATCH_MP_TAC
   (REWRITE_RULE[candle_q_real_head_def]
     (SPECL
       [`candle_q_interval_run ienv (candle_poly_compile e) []`;
        `[candle_poly_value_list env e]`]
       candle_q_stack_head_contains)) THEN
  MP_TAC
   (SPECL
     [`candle_poly_compile e`;
      `ienv:(((num#num)#num)#((num#num)#num))list`;
      `env:real list`;
      `[]:(((num#num)#num)#((num#num)#num))list`;
      `[]:real list`]
     candle_q_interval_run_sound) THEN
  ASM_REWRITE_TAC[candle_q_stack_contains_def;
                  candle_poly_compile_real_program]);;

let candle_poly_diff_interval_sound = prove
 (`!e ienv env di.
     candle_q_stack_contains ienv env
     ==> candle_q_interval_contains
          (candle_q_program_interval ienv
            (candle_poly_compile (candle_poly_diff di e)))
          (candle_poly_d_list di env e)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_q_program_interval_def] THEN
  MATCH_MP_TAC
   (REWRITE_RULE[candle_q_real_head_def]
     (SPECL
       [`candle_q_interval_run ienv
          (candle_poly_compile (candle_poly_diff di e)) []`;
        `[candle_poly_d_list di env e]`]
       candle_q_stack_head_contains)) THEN
  MP_TAC
   (SPECL
     [`candle_poly_compile (candle_poly_diff di e)`;
      `ienv:(((num#num)#num)#((num#num)#num))list`;
      `env:real list`;
      `[]:(((num#num)#num)#((num#num)#num))list`;
      `[]:real list`]
     candle_q_interval_run_sound) THEN
  ASM_REWRITE_TAC[candle_q_stack_contains_def;
                  candle_poly_diff_compile_real_program]);;

let candle_poly_diff2_interval_sound = prove
 (`!e ienv env di dj.
     candle_q_stack_contains ienv env
     ==> candle_q_interval_contains
          (candle_q_program_interval ienv
            (candle_poly_compile (candle_poly_diff2 dj di e)))
          (candle_poly_dd_list dj di env e)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_q_program_interval_def] THEN
  MATCH_MP_TAC
   (REWRITE_RULE[candle_q_real_head_def]
     (SPECL
       [`candle_q_interval_run ienv
          (candle_poly_compile (candle_poly_diff2 dj di e)) []`;
        `[candle_poly_dd_list dj di env e]`]
       candle_q_stack_head_contains)) THEN
  MP_TAC
   (SPECL
     [`candle_poly_compile (candle_poly_diff2 dj di e)`;
      `ienv:(((num#num)#num)#((num#num)#num))list`;
      `env:real list`;
      `[]:(((num#num)#num)#((num#num)#num))list`;
      `[]:real list`]
     candle_q_interval_run_sound) THEN
  ASM_REWRITE_TAC[candle_q_stack_contains_def;
                  candle_poly_diff2_compile_real_program]);;

let candle_all2_list_of_seq = prove
 (`!P n (f:num->A) (g:num->B).
     ALL2 P (list_of_seq f n) (list_of_seq g n) <=>
     (!i. i < n ==> P (f i) (g i))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `MAP (f:num->A) (list_of_seq (I:num->num) n) = list_of_seq f n`
   (fun th -> ONCE_REWRITE_TAC[GSYM th]) THENL
   [REWRITE_TAC[MAP_LIST_OF_SEQ; I_O_ID]; ALL_TAC] THEN
  SUBGOAL_THEN
   `MAP (g:num->B) (list_of_seq (I:num->num) n) = list_of_seq g n`
   (fun th -> ONCE_REWRITE_TAC[GSYM th]) THENL
   [REWRITE_TAC[MAP_LIST_OF_SEQ; I_O_ID]; ALL_TAC] THEN
  REWRITE_TAC[ALL2_MAP2; ALL2_ALL; GSYM ALL_EL;
              LENGTH_LIST_OF_SEQ] THEN
  SIMP_TAC[EL_LIST_OF_SEQ; I_THM]);;

let candle_q_program_interval_list_map = prove
 (`!ienv programs.
     candle_q_program_interval_list ienv programs =
     MAP (candle_q_program_interval ienv) programs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_q_program_interval_list_def; MAP]);;

let candle_q_program_interval_matrix_map = prove
 (`!ienv program_matrix.
     candle_q_program_interval_matrix ienv program_matrix =
     MAP (candle_q_program_interval_list ienv) program_matrix`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_q_program_interval_matrix_def; MAP]);;

let candle_q_stack_contains_all2 = prove
 (`!intervals values.
     candle_q_stack_contains intervals values <=>
     ALL2 candle_q_interval_contains intervals values`,
  LIST_INDUCT_TAC THEN
  X_GEN_TAC `values:real list` THEN
  MP_TAC (ISPEC `values:real list` list_CASES) THEN
  DISCH_THEN
   (DISJ_CASES_THEN2 SUBST_ALL_TAC
     (X_CHOOSE_THEN `value:real`
       (X_CHOOSE_THEN `values':real list` SUBST_ALL_TAC))) THEN
  ASM_REWRITE_TAC[candle_q_stack_contains_def; ALL2]);;

let candle_poly_gradient_programs_interval_sound = prove
 (`!nvars e ienv env.
     candle_q_stack_contains ienv env
     ==>
     ALL2 candle_q_interval_contains
       (candle_q_program_interval_list ienv
         (candle_poly_gradient_programs nvars e))
       (candle_poly_gradient nvars env e)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_q_program_interval_list_map;
              candle_poly_gradient_programs_def;
              candle_poly_gradient_def; MAP_LIST_OF_SEQ; o_THM;
              candle_all2_list_of_seq] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC candle_poly_diff_interval_sound THEN ASM_REWRITE_TAC[]);;

let candle_poly_hessian_programs_interval_sound = prove
 (`!nvars e ienv env.
     candle_q_stack_contains ienv env
     ==>
     ALL2 candle_q_stack_contains
       (candle_q_program_interval_matrix ienv
         (candle_poly_hessian_programs nvars e))
       (candle_poly_hessian nvars env e)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_q_program_interval_matrix_map;
              candle_poly_hessian_programs_def;
              candle_poly_hessian_def; MAP_LIST_OF_SEQ; o_THM;
              candle_all2_list_of_seq] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_q_program_interval_list_map; MAP_LIST_OF_SEQ; o_THM;
              candle_q_stack_contains_all2; candle_all2_list_of_seq] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC candle_poly_diff2_interval_sound THEN ASM_REWRITE_TAC[]);;

end;;
