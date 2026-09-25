(* ========================================================================== *)
(* Reflected execution of a complete pi/2 + atn analytic-expression program. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_program_compute.ml";;

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

let candle_analytic_expr_atn_program_axioms_before = axioms ();;

let candle_analytic_expr_atn_program_expression =
 `Candle_analytic_add Candle_analytic_pi_half
    (Candle_analytic_atn
      (Candle_analytic_poly (Candle_poly_var 0)))`;;

let candle_analytic_expr_atn_program_boxes =
 `([(((1,0),1),((1,0),1))]:
    (((num#num)#num)#((num#num)#num))list)`;;

let candle_analytic_expr_atn_program_boxes_encoded =
  rand
    (concl
      (REWRITE_CONV
        [candle_cv_q_interval_list_def; candle_cv_q_interval_def;
         candle_cv_q_def; candle_cv_lc_z_def; FST; SND]
        (mk_comb (`candle_cv_q_interval_list`,
          candle_analytic_expr_atn_program_boxes))));;

let candle_analytic_expr_atn_program_encoded =
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
            candle_analytic_expr_atn_program_expression)))));;

let candle_analytic_expr_atn_program_started = Unix.gettimeofday ();;

let candle_analytic_expr_atn_program_result =
  Kernel.compute
    (COMPUTE_INIT_THMS,candle_cv_q_dim_analytic_program_compute_eqs)
    (list_mk_comb
      (`candle_cv_q_dim_analytic_program`,
       [candle_analytic_expr_atn_program_boxes_encoded;
        candle_analytic_expr_atn_program_encoded]));;

let candle_analytic_expr_atn_program_representation =
  REWRITE_RULE
    [candle_cv_q_interval_list_def; candle_cv_q_interval_def;
     candle_cv_q_def; candle_cv_lc_z_def;
     candle_analytic_compile_def; candle_poly_compile_def; APPEND;
     candle_cv_analytic_instruction_list_def;
     candle_cv_analytic_instruction_def;
     candle_cv_q_instruction_list_def; candle_cv_q_instruction_def;
     FST; SND]
    (SPECL
      [candle_analytic_expr_atn_program_expression;
       candle_analytic_expr_atn_program_boxes]
      candle_cv_q_dim_analytic_compile_program_correct);;

let candle_analytic_expr_atn_program_data =
  TRANS (SYM candle_analytic_expr_atn_program_representation)
    candle_analytic_expr_atn_program_result;;

let candle_analytic_expr_atn_program_bool_decision = prove
 (`!p. ((if p then 1 else 0) = 1) <=> p`,
  GEN_TAC THEN BOOL_CASES_TAC `p:bool` THEN REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_analytic_expr_atn_program_domain =
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
      candle_analytic_expr_atn_program_data in
  REWRITE_RULE[candle_analytic_expr_atn_program_bool_decision]
    (CONJUNCT1 result);;

let candle_analytic_expr_atn_program_stack = prove
 (`candle_q_stack_contains
    [(((1,0),1),((1,0),1))] [&1 / &2]`,
  REWRITE_TAC[candle_q_stack_contains_def;
              candle_q_interval_contains_def; candle_q_real_def;
              candle_q_den_def; candle_lc_zreal_def; FST; SND] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let candle_analytic_expr_atn_program_sound =
  MATCH_MP
    (SPECL
      [candle_analytic_expr_atn_program_expression;
       candle_analytic_expr_atn_program_boxes; `[&1 / &2]`]
      candle_q_dim_analytic_jet_sound)
    (CONJ candle_analytic_expr_atn_program_stack
      candle_analytic_expr_atn_program_domain);;

let candle_analytic_expr_atn_program_length =
  prove
   (`LENGTH
      (candle_analytic_compile
        (Candle_analytic_add Candle_analytic_pi_half
          (Candle_analytic_atn
            (Candle_analytic_poly (Candle_poly_var 0))))) = 4`,
    REWRITE_TAC[candle_analytic_compile_def; candle_poly_compile_def;
                APPEND; LENGTH] THEN
    CONV_TAC NUM_REDUCE_CONV);;

let candle_analytic_expr_atn_program_seconds =
  Unix.gettimeofday () -. candle_analytic_expr_atn_program_started;;

if hyp candle_analytic_expr_atn_program_result <> [] ||
   hyp candle_analytic_expr_atn_program_representation <> [] ||
   hyp candle_analytic_expr_atn_program_domain <> [] ||
   hyp candle_analytic_expr_atn_program_sound <> [] ||
   not (aconv (rand (concl candle_analytic_expr_atn_program_length)) `4`) then
  failwith "analytic atn/pi program: proof or instruction mismatch";;

let candle_analytic_expr_atn_program_axioms_after = axioms ();;
if length candle_analytic_expr_atn_program_axioms_after <>
     length candle_analytic_expr_atn_program_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_analytic_expr_atn_program_axioms_before)
       candle_analytic_expr_atn_program_axioms_after) then
  failwith "analytic atn/pi program: changed the global axiom set";;

let _ = print_endline
  ("CANDLE_CV_ANALYTIC_EXPR_ATN_PROGRAM_RESULT dimensions=1 " ^
   "instructions=4 domain=1 semantic=1 seconds=" ^
   string_of_float candle_analytic_expr_atn_program_seconds ^
   " output_md5=" ^
   Digest.to_hex
     (Digest.string (string_of_thm candle_analytic_expr_atn_program_result)));;
let _ = print_endline "CANDLE_CV_ANALYTIC_EXPR_ATN_PROGRAM_OK";;
