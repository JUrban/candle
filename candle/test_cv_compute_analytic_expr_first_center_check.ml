(* Load-and-contract regression for the Hessian-free analytic center checker. *)

needs "candle/cv_compute_analytic_expr_first_center_check.ml";;

open Candle_cv_analytic_expr_first_center_check;;

if hyp candle_cv_q_dim_analytic_first_center_check_correct <> [] then
  failwith "analytic first-center checker correctness has assumptions";;

if not
    (mem candle_cv_q_dim_analytic_first_center_check_def
      candle_cv_q_dim_analytic_first_center_compute_eqs) then
  failwith "analytic first-center checker equation missing";;

print_endline "CANDLE_CV_ANALYTIC_FIRST_CENTER_CHECK_OK";;
