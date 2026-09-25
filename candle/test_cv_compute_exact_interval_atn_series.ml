(* ========================================================================== *)
(* Focused reflected arctangent-series interval regression.                  *)
(* ========================================================================== *)

needs "candle/cv_compute_exact_interval_atn_series.ml";;

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
let candle_atn_series_axioms_before = axioms ();;

let candle_atn_series_input =
 `((((0,1),15),((9,0),15)):
   ((num#num)#num)#((num#num)#num))`;;

let candle_atn_series_bad_input =
 `((((0,1),0),((1,0),0)):
   ((num#num)#num)#((num#num)#num))`;;

let candle_atn_series_representation input =
  REWRITE_CONV
    [candle_cv_q_interval_def; candle_cv_q_def; candle_cv_lc_z_def;
     FST; SND]
    (mk_comb (`candle_cv_q_interval`,input));;

let candle_atn_series_input_representation =
  candle_atn_series_representation candle_atn_series_input;;

let candle_atn_series_bad_input_representation =
  candle_atn_series_representation candle_atn_series_bad_input;;

let candle_atn_series_flag_accept = prove
 (`!b. Cexp_num (if b then 1 else 0) = Cexp_num 1 ==> b`,
  GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[injectivity "cval"] THEN ARITH_TAC);;

let candle_atn_series_started = Unix.gettimeofday ();;

let candle_atn_series_domain_compute =
  Kernel.compute
    (COMPUTE_INIT_THMS,candle_cv_q_atn_series_compute_eqs)
    (mk_comb
      (`candle_cv_q_interval_atn_series_domain`,
       rand (concl candle_atn_series_input_representation)));;

let candle_atn_series_domain_link =
  TRANS
    (SYM
      (SPEC candle_atn_series_input
        candle_cv_q_interval_atn_series_domain_correct))
    (TRANS
      (AP_TERM `candle_cv_q_interval_atn_series_domain`
        candle_atn_series_input_representation)
      candle_atn_series_domain_compute);;

let candle_atn_series_domain =
  MATCH_MP candle_atn_series_flag_accept candle_atn_series_domain_link;;

let candle_atn_series_output_compute =
  Kernel.compute
    (COMPUTE_INIT_THMS,candle_cv_q_atn_series_compute_eqs)
    (mk_comb
      (`candle_cv_q_interval_atn_series`,
       rand (concl candle_atn_series_input_representation)));;

let candle_atn_series_output_link =
  TRANS
    (SYM
      (SPEC candle_atn_series_input
        candle_cv_q_interval_atn_series_correct))
    (TRANS
      (AP_TERM `candle_cv_q_interval_atn_series`
        candle_atn_series_input_representation)
      candle_atn_series_output_compute);;

let candle_atn_series_bad_domain_compute =
  Kernel.compute
    (COMPUTE_INIT_THMS,candle_cv_q_atn_series_compute_eqs)
    (mk_comb
      (`candle_cv_q_interval_atn_series_domain`,
       rand (concl candle_atn_series_bad_input_representation)));;

let candle_atn_series_sound =
  let x = `x:real` in
  let membership =
    mk_comb
      (mk_comb (`candle_q_interval_contains`,candle_atn_series_input),x) in
  let theorem =
    MATCH_MP
      (SPECL [candle_atn_series_input;x]
        candle_q_interval_atn_series_sound)
      (CONJ candle_atn_series_domain (ASSUME membership)) in
  GEN x (DISCH membership theorem);;

let candle_atn_series_seconds =
  Unix.gettimeofday () -. candle_atn_series_started;;

if hyp candle_atn_series_domain <> [] ||
   hyp candle_atn_series_output_compute <> [] ||
   hyp candle_atn_series_output_link <> [] ||
   hyp candle_atn_series_bad_domain_compute <> [] ||
   hyp candle_atn_series_sound <> [] ||
   rand (concl candle_atn_series_domain_compute) <> `Cexp_num 1` ||
   rand (concl candle_atn_series_bad_domain_compute) <> `Cexp_num 0` then
  failwith "reflected atn series: theorem or domain mismatch";;

let candle_atn_series_axioms_after = axioms ();;
if length candle_atn_series_axioms_after <>
     length candle_atn_series_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_atn_series_axioms_before)
       candle_atn_series_axioms_after) then
  failwith "reflected atn series: changed the global axiom set";;

let _ =
  print_endline
    ("CANDLE_CV_EXACT_INTERVAL_ATN_SERIES_RESULT terms_lower=6 " ^
     "terms_upper=7 domain=1 rejected_boundary=1 sound=1 seconds=" ^
     string_of_float candle_atn_series_seconds ^ " output_md5=" ^
     Digest.to_hex
       (Digest.string (string_of_thm candle_atn_series_output_compute)));;

let _ = print_endline "CANDLE_CV_EXACT_INTERVAL_ATN_SERIES_OK";;
