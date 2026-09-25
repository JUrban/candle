(* Focused regression for certificate-independent analytic semantics. *)

needs "candle/cv_compute_analytic_expr_certificate_erasure.ml";;

open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_certificate_erasure;;

let candle_analytic_erasure_left =
 `Candle_analytic_sqrt 1 2 3 4 5 6
    (Candle_analytic_atn Candle_analytic_pi_half)`;;
let candle_analytic_erasure_right =
 `Candle_analytic_sqrt 7 8 9 10 11 12
    (Candle_analytic_atn Candle_analytic_pi_half)`;;

let candle_analytic_erasure_identity = prove
 (mk_eq
   (mk_comb
     (`candle_analytic_erase_sqrt_certificates`,
      candle_analytic_erasure_left),
    mk_comb
     (`candle_analytic_erase_sqrt_certificates`,
      candle_analytic_erasure_right)),
  REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def]);;

let candle_analytic_erasure_denotation =
  MATCH_MP
    (SPECL
      [candle_analytic_erasure_left;candle_analytic_erasure_right]
      (INST_TYPE [`:6`,`:N`]
        candle_analytic_denote_certificate_transport))
    candle_analytic_erasure_identity;;

if hyp candle_analytic_erase_valid_dim <> [] ||
   hyp candle_analytic_erase_value <> [] ||
   hyp candle_analytic_erase_d <> [] ||
   hyp candle_analytic_erase_dd <> [] ||
   hyp candle_q_dim_analytic_contains_certificate_transport <> [] ||
   hyp candle_analytic_erasure_denotation <> [] then
  failwith "analytic certificate erasure: theorem assumptions";;

print_endline "CANDLE_CV_ANALYTIC_CERTIFICATE_ERASURE_OK";;
