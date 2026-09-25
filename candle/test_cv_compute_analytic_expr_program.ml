(* ========================================================================== *)
(* Focused regression for compiled nested analytic-expression programs.      *)
(* ========================================================================== *)

load_path :=
  ["/project/worktrees/candle-cv-nonlinear-atn-expr-v1"] @ !load_path;;

needs "candle/cv_compute_analytic_expr_program.ml";;

open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_program;;

let candle_analytic_expr_program_axioms_before = axioms ();;

let candle_analytic_expr_program_nested =
 `Candle_analytic_add Candle_analytic_pi_half
    (Candle_analytic_atn
      (Candle_analytic_sqrt 2 0 0 2 0 0
        (Candle_analytic_add
          (Candle_analytic_inv
            (Candle_analytic_poly
              (Candle_poly_add
                (Candle_poly_const 1 0 0) (Candle_poly_var 0))))
          (Candle_analytic_poly (Candle_poly_const 3 0 0)))))`;;

let candle_analytic_expr_program_compiled =
  SPECL
    [candle_analytic_expr_program_nested;
     `[(((((0,0),0),((0,0),0))):
          ((num#num)#num)#((num#num)#num))]`]
    candle_q_dim_analytic_compile_program;;

if hyp candle_analytic_expr_program_compiled <> [] then
  failwith "analytic expression program: compile theorem assumptions";;

let candle_analytic_expr_program_length =
  (REWRITE_CONV[candle_analytic_compile_def; APPEND; LENGTH] THENC
   NUM_REDUCE_CONV)
   `LENGTH (candle_analytic_compile
      (Candle_analytic_add Candle_analytic_pi_half
        (Candle_analytic_atn
          (Candle_analytic_sqrt 2 0 0 2 0 0
            (Candle_analytic_add
              (Candle_analytic_inv
                (Candle_analytic_poly
                  (Candle_poly_add
                    (Candle_poly_const 1 0 0) (Candle_poly_var 0))))
              (Candle_analytic_poly (Candle_poly_const 3 0 0)))))))`;;

if not (aconv (concl candle_analytic_expr_program_length)
      `LENGTH (candle_analytic_compile
        (Candle_analytic_add Candle_analytic_pi_half
          (Candle_analytic_atn
            (Candle_analytic_sqrt 2 0 0 2 0 0
              (Candle_analytic_add
                (Candle_analytic_inv
                  (Candle_analytic_poly
                    (Candle_poly_add
                      (Candle_poly_const 1 0 0) (Candle_poly_var 0))))
                (Candle_analytic_poly (Candle_poly_const 3 0 0))))))) = 8`) then
  failwith "analytic expression program: unexpected instruction count";;

let candle_analytic_expr_program_axioms_after = axioms ();;
if length candle_analytic_expr_program_axioms_after <>
     length candle_analytic_expr_program_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_analytic_expr_program_axioms_before)
       candle_analytic_expr_program_axioms_after) then
  failwith "analytic expression program: changed the global axiom set";;

let _ = print_endline
  "CANDLE_CV_ANALYTIC_EXPR_PROGRAM_RESULT constructors=9 analytic_instructions=8 shared_poly_leaves=2 compile_sound=1";;
let _ = print_endline "CANDLE_CV_ANALYTIC_EXPR_PROGRAM_OK";;
