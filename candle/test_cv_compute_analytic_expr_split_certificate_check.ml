(* Focused regression for separate center/whole-box sqrt certificates. *)

needs "candle/cv_compute_analytic_expr_split_certificate_check.ml";;

open Candle_cv_analytic_expr_split_certificate_check;;

if hyp candle_cv_q_dim_analytic_split_certificate_check_correct <> [] ||
   hyp candle_q_dim_analytic_split_certificate_upper_sound <> [] ||
   hyp candle_q_dim_analytic_split_certificate_accept_sound <> [] then
  failwith "analytic split-certificate checker: theorem assumptions";;

print_endline "CANDLE_CV_ANALYTIC_SPLIT_CERTIFICATE_CHECK_OK";;
