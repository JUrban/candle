needs "candle/compute.ml";;
needs "candle/cv_compute_polynomial_expr_jet.ml";;

open Candle_cv_exact_interval_program;;
open Candle_cv_exact_rational_core;;
open Candle_cv_whole_box_jet;;
open Candle_cv_polynomial_expr_jet;;

let candle_poly_cubic_expr =
  `Candle_poly_add
     (Candle_poly_add
       (Candle_poly_mul
         (Candle_poly_square (Candle_poly_var 0)) (Candle_poly_var 0))
       (Candle_poly_mul
         (Candle_poly_var 0) (Candle_poly_square (Candle_poly_var 1))))
     (Candle_poly_neg (Candle_poly_const 1 0 0))`;;

let candle_poly_cubic_program =
  rand (concl (REWRITE_CONV[candle_poly_compile_def; APPEND]
    (mk_comb (`candle_poly_compile`,candle_poly_cubic_expr))));;

let candle_poly_cubic_expected_program =
  `[Candle_q_load 0; Candle_q_square; Candle_q_load 0; Candle_q_mul;
    Candle_q_load 0; Candle_q_load 1; Candle_q_square; Candle_q_mul;
    Candle_q_add; Candle_q_push 1 0 0; Candle_q_neg; Candle_q_add]`;;

if length (dest_list candle_poly_cubic_program) <> 12 ||
   not (aconv candle_poly_cubic_program candle_poly_cubic_expected_program)
then failwith "polynomial AST cubic compiler output mismatch";;

let candle_poly_cubic_valid = prove
 (`candle_poly_valid_2
     (Candle_poly_add
       (Candle_poly_add
         (Candle_poly_mul
           (Candle_poly_square (Candle_poly_var 0))
           (Candle_poly_var 0))
         (Candle_poly_mul
           (Candle_poly_var 0)
           (Candle_poly_square (Candle_poly_var 1))))
       (Candle_poly_neg (Candle_poly_const 1 0 0)))`,
  REWRITE_TAC[candle_poly_valid_2_def] THEN ARITH_TAC);;

let candle_poly_out_of_range_rejected = prove
 (`~candle_poly_valid_2 (Candle_poly_var 2)`,
  REWRITE_TAC[candle_poly_valid_2_def] THEN ARITH_TAC);;

let candle_poly_cubic_compiled_correct =
  SPECL [candle_poly_cubic_expr; `x:real`; `y:real`]
    candle_poly_compile_correct;;

if hyp candle_poly_real_jet_correct <> [] ||
   hyp candle_poly_compile_run <> [] ||
   hyp candle_poly_compile_program <> [] ||
   hyp candle_poly_compile_correct <> [] ||
   hyp candle_poly_cubic_valid <> [] ||
   hyp candle_poly_out_of_range_rejected <> [] ||
   hyp candle_poly_cubic_compiled_correct <> []
then failwith "polynomial AST jet theorem assumptions mismatch";;

print_endline "CANDLE_CV_POLYNOMIAL_EXPR_JET_OK";;
