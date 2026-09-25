(* Focused regression for extended-normalization Taylor accumulation. *)

needs "candle/cv_compute_analytic_expr_extended_taylor.ml";;

open Candle_cv_analytic_expr_extended_taylor;;

if hyp candle_q_dim_taylor_upper_extended_real <> [] ||
   hyp candle_cv_q_dot_abs_upper_extended_correct <> [] ||
   hyp candle_cv_q_weighted_rows_abs_upper_extended_correct <> [] ||
   hyp candle_cv_q_dim_taylor_upper_extended_correct <> [] then
  failwith "analytic extended Taylor: theorem assumptions";;

print_endline "CANDLE_CV_ANALYTIC_EXTENDED_TAYLOR_OK";;
