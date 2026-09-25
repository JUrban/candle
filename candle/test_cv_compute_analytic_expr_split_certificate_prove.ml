(* Focused load regression for the split-certificate theorem adapter. *)

needs "candle/cv_compute_analytic_expr_split_certificate_prove.ml";;

open Candle_cv_analytic_expr_split_certificate_prove;;

if hyp candle_q_dim_analytic_split_certificate_sound_six <> [] then
  failwith "analytic split-certificate prover: soundness assumptions";;

print_endline "CANDLE_CV_ANALYTIC_SPLIT_CERTIFICATE_PROVE_OK";;
