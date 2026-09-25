(* ========================================================================== *)
(* Complete reflected proof of a small nested analytic whole-box inequality. *)
(* ========================================================================== *)

load_path :=
  ["/project/worktrees/candle-cv-nonlinear-whole-box-v1"] @ !load_path;;

needs "candle/cv_compute_analytic_expr_jet_check.ml";;

open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_jet_check;;

module Candle_cv_analytic_expr_jet_check_test = struct

let candle_analytic_jet_check_axioms_before = axioms ();;
let _ = print_endline "CANDLE_CV_ANALYTIC_JET_CHECK_PHASE preparation-begin";;

let candle_analytic_jet_check_expression =
 `Candle_analytic_add
    (Candle_analytic_sqrt 2 0 0 2 0 0
      (Candle_analytic_add
        (Candle_analytic_inv
          (Candle_analytic_poly
            (Candle_poly_add
              (Candle_poly_const 1 0 0) (Candle_poly_var 0))))
        (Candle_analytic_poly (Candle_poly_const 3 0 0))))
    (Candle_analytic_neg
      (Candle_analytic_poly (Candle_poly_const 3 0 0)))`;;

let candle_analytic_jet_check_boxes =
 `[(((((0,0),0),((0,0),0))):
      ((num#num)#num)#((num#num)#num))]`;;

let candle_analytic_jet_check_program_representation =
  REWRITE_CONV
    [candle_analytic_compile_def; candle_poly_compile_def; APPEND;
     candle_cv_analytic_instruction_list_def;
     candle_cv_analytic_instruction_def;
     candle_cv_q_instruction_list_def; candle_cv_q_instruction_def;
     candle_analytic_sqrt_interval_def;
     candle_cv_q_interval_def; candle_cv_q_def; candle_cv_lc_z_def;
     FST; SND]
    (mk_comb
      (`candle_cv_analytic_instruction_list`,
       mk_comb (`candle_analytic_compile`,
         candle_analytic_jet_check_expression)));;

let candle_analytic_jet_check_boxes_representation =
  REWRITE_CONV
    [candle_cv_q_interval_list_def; candle_cv_q_interval_def;
     candle_cv_q_def; candle_cv_lc_z_def; FST; SND]
    (mk_comb (`candle_cv_q_interval_list`,
      candle_analytic_jet_check_boxes));;

let candle_analytic_jet_check_program_encoded =
  rand (concl candle_analytic_jet_check_program_representation);;
let candle_analytic_jet_check_boxes_encoded =
  rand (concl candle_analytic_jet_check_boxes_representation);;

let candle_analytic_jet_check_compute_term =
  list_mk_comb
    (`candle_cv_q_dim_analytic_jet_whole_box_check`,
     [candle_analytic_jet_check_program_encoded;
      candle_analytic_jet_check_boxes_encoded]);;

let _ = print_endline "CANDLE_CV_ANALYTIC_JET_CHECK_PHASE preparation-end";;
let _ = print_endline "CANDLE_CV_ANALYTIC_JET_CHECK_PHASE compute-begin";;
let candle_analytic_jet_check_compute_theorem =
  Kernel.compute
    (COMPUTE_INIT_THMS,candle_cv_q_dim_analytic_jet_compute_eqs)
    candle_analytic_jet_check_compute_term;;
let _ = print_endline "CANDLE_CV_ANALYTIC_JET_CHECK_PHASE compute-end";;

let candle_analytic_jet_check_result =
  rand (concl candle_analytic_jet_check_compute_theorem);;
let candle_analytic_jet_check_result_left,
    candle_analytic_jet_check_result_right =
  let partial,right = dest_comb candle_analytic_jet_check_result in
  let operator,left = dest_comb partial in
  if aconv operator `Cexp_pair` then left,right
  else failwith "analytic shared-jet checker: result is not a pair";;

if not (aconv candle_analytic_jet_check_result_left `Cexp_num 1`) then
  failwith "analytic shared-jet checker: numerical check rejected";;
if not
    (aconv candle_analytic_jet_check_result_right
      `Cexp_pair (Cexp_pair (Cexp_num 0) (Cexp_num 2048))
        (Cexp_num 2047)`) then
  failwith "analytic shared-jet checker: unexpected exact upper bound";;

let _ = print_endline "CANDLE_CV_ANALYTIC_JET_CHECK_PHASE handoff-begin";;

let candle_analytic_jet_check_abstract_compute =
  PURE_REWRITE_RULE
    [SYM candle_analytic_jet_check_program_representation;
     SYM candle_analytic_jet_check_boxes_representation]
    candle_analytic_jet_check_compute_theorem;;

let candle_analytic_jet_check_correctness =
  SPECL
    [candle_analytic_jet_check_expression;
     candle_analytic_jet_check_boxes]
    candle_cv_q_dim_analytic_jet_whole_box_check_correct;;

let candle_analytic_jet_check_accept_encoding =
  TRANS (SYM candle_analytic_jet_check_abstract_compute)
    candle_analytic_jet_check_correctness;;

let candle_analytic_jet_check_numerical_goal =
  list_mk_comb
    (`candle_q_dim_analytic_jet_whole_box_numerical_accept`,
     [candle_analytic_jet_check_expression;
      candle_analytic_jet_check_boxes]);;

let candle_analytic_jet_check_flag_accept = prove
 (`!b. (1:num) = (if b then 1 else 0) ==> b`,
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_analytic_jet_check_flag_theorem =
  let th =
    REWRITE_RULE[cexp_fst_def; injectivity "cval"; SYM ONE]
      (AP_TERM `Cexp_fst` candle_analytic_jet_check_accept_encoding) in
  let expected =
    mk_eq (`1`,mk_cond (candle_analytic_jet_check_numerical_goal,`1`,`0`)) in
  if aconv (concl th) expected then th
  else if aconv (concl th) (mk_eq (rand expected,lhand expected)) then SYM th
  else failwith "analytic shared-jet checker: numerical flag mismatch";;

let candle_analytic_jet_check_numerical_theorem =
  MATCH_MP
    (SPEC candle_analytic_jet_check_numerical_goal
      candle_analytic_jet_check_flag_accept)
    candle_analytic_jet_check_flag_theorem;;

let candle_analytic_jet_check_valid = prove
 (`candle_analytic_valid_dim 1
     (Candle_analytic_add
       (Candle_analytic_sqrt 2 0 0 2 0 0
         (Candle_analytic_add
           (Candle_analytic_inv
             (Candle_analytic_poly
               (Candle_poly_add
                 (Candle_poly_const 1 0 0) (Candle_poly_var 0))))
           (Candle_analytic_poly (Candle_poly_const 3 0 0))))
       (Candle_analytic_neg
         (Candle_analytic_poly (Candle_poly_const 3 0 0))))`,
  REWRITE_TAC[candle_analytic_valid_dim_def; candle_poly_valid_dim_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_analytic_jet_check_length = prove
 (`LENGTH
    [(((((0,0),0),((0,0),0))):
       ((num#num)#num)#((num#num)#num))] = 1`,
  REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let candle_analytic_jet_check_sound_one =
  REWRITE_RULE[DIMINDEX_1]
    (INST_TYPE [`:1`,`:N`]
      candle_q_dim_analytic_jet_whole_box_accept_sound);;

let candle_analytic_jet_check_final_theorem =
  MATCH_MP
    (SPECL
      [candle_analytic_jet_check_expression;
       candle_analytic_jet_check_boxes]
      candle_analytic_jet_check_sound_one)
    (CONJ candle_analytic_jet_check_valid
      (CONJ candle_analytic_jet_check_length
        candle_analytic_jet_check_numerical_theorem));;

if hyp candle_analytic_jet_check_compute_theorem <> [] ||
   hyp candle_analytic_jet_check_numerical_theorem <> [] ||
   hyp candle_analytic_jet_check_final_theorem <> [] then
  failwith "analytic shared-jet checker: proof assumptions";;

let candle_analytic_jet_check_axioms_after = axioms ();;
if length candle_analytic_jet_check_axioms_after <>
     length candle_analytic_jet_check_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_analytic_jet_check_axioms_before)
       candle_analytic_jet_check_axioms_after) then
  failwith "analytic shared-jet checker: changed the global axiom set";;

let _ = print_endline "CANDLE_CV_ANALYTIC_JET_CHECK_PHASE handoff-end";;
let _ = print_endline
  "CANDLE_CV_ANALYTIC_JET_CHECK_RESULT dimensions=1 analytic_instructions=8 domain_guards=2 upper=-2048/2048 accepted=1 source_theorem=1";;
let _ = print_endline "CANDLE_CV_ANALYTIC_JET_CHECK_OK";;

end;;
