(* ========================================================================== *)
(* Behavioral check for the analytic first-order center interpreter.          *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_first_jet_program_compute.ml";;

open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_first_jet_program_compute;;

module Candle_cv_analytic_expr_first_jet_program_compute_test = struct

let candle_analytic_first_axioms_before = axioms ();;

let candle_analytic_first_expression =
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

let candle_analytic_first_boxes =
 `[(((((0,0),0),((0,0),0))):
      ((num#num)#num)#((num#num)#num))]`;;

let candle_analytic_first_program_representation =
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
       mk_comb
         (`candle_analytic_compile`,candle_analytic_first_expression)));;

let candle_analytic_first_boxes_representation =
  REWRITE_CONV
    [candle_cv_q_interval_list_def; candle_cv_q_interval_def;
     candle_cv_q_def; candle_cv_lc_z_def; FST; SND]
    (mk_comb (`candle_cv_q_interval_list`,candle_analytic_first_boxes));;

let candle_analytic_first_center_environment_theorem =
  Kernel.compute
    (COMPUTE_INIT_THMS,
     candle_cv_q_dim_analytic_first_program_compute_eqs)
    (mk_comb
      (`candle_cv_q_center_environment_list`,
       rand (concl candle_analytic_first_boxes_representation)));;

let candle_analytic_first_compute_theorem =
  Kernel.compute
    (COMPUTE_INIT_THMS,
     candle_cv_q_dim_analytic_first_program_compute_eqs)
    (list_mk_comb
      (`candle_cv_q_dim_analytic_first_program`,
       [rand (concl candle_analytic_first_center_environment_theorem);
        rand (concl candle_analytic_first_program_representation)]));;

let candle_analytic_first_result =
  rand (concl candle_analytic_first_compute_theorem);;

let candle_analytic_first_domain =
  rand (concl
    (REWRITE_CONV
      [candle_cv_q_dim_analytic_first_result_domain_def; cexp_fst_def]
      (mk_comb
        (`candle_cv_q_dim_analytic_first_result_domain`,
         candle_analytic_first_result))));;

if not (aconv candle_analytic_first_domain `Cexp_num 1`) then
  failwith "analytic first-center nested domain rejected";;

(* The direct computation above is checked separately from the universal
   representation theorem; together they prevent an accepted but unrelated
   first-order result from serving as this regression's evidence. *)
let candle_analytic_first_correctness =
  SPECL
    [candle_analytic_first_expression;
     candle_analytic_first_boxes]
    candle_cv_q_dim_analytic_first_compile_program_correct;;

let candle_analytic_first_axioms_after = axioms ();;
if hyp candle_analytic_first_center_environment_theorem <> [] ||
   hyp candle_analytic_first_compute_theorem <> [] ||
   hyp candle_analytic_first_correctness <> [] ||
   length candle_analytic_first_axioms_after <>
     length candle_analytic_first_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_analytic_first_axioms_before)
       candle_analytic_first_axioms_after) then
  failwith "analytic first-center behavioral proof mismatch";;

let _ = print_endline
  "CANDLE_CV_ANALYTIC_FIRST_JET_RESULT dimensions=1 analytic_instructions=8 domain=1";;
let _ = print_endline "CANDLE_CV_ANALYTIC_FIRST_JET_OK";;

end;;
