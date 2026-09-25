(* Load-and-contract regression for the Hessian-free analytic center checker. *)

needs "candle/cv_compute_analytic_expr_first_center_check.ml";;

open Candle_cv_analytic_expr_first_center_check;;

if hyp candle_cv_q_dim_analytic_first_center_check_correct <> [] then
  failwith "analytic first-center checker correctness has assumptions";;

let candle_analytic_first_center_equation_smoke =
  Kernel.compute
    (COMPUTE_INIT_THMS,
     candle_cv_q_dim_analytic_first_center_compute_eqs)
    `candle_cv_q_dim_analytic_first_center_check
       (Cexp_num 0) (Cexp_num 0)`;;

if hyp candle_analytic_first_center_equation_smoke <> [] then
  failwith "analytic first-center checker equation has assumptions";;

print_endline "CANDLE_CV_ANALYTIC_FIRST_CENTER_CHECK_OK";;
