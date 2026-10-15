(* ========================================================================== *)
(* Focused exact-rational regression for the crossing-zero [matan] packet.   *)
(*                                                                            *)
(* Loaded after [cv_compute_exact_interval_matan_series.ml] in the focused    *)
(* action-296 checkpoint harness.                                             *)
(* ========================================================================== *)

open Candle_cv_exact_interval_matan_series;;

let candle_matan_series_test_axioms_before = axioms ();;

let candle_matan_series_input_symmetric =
 `(((((0,1),4):(num#num)#num),(((1,0),4):(num#num)#num)):
    ((num#num)#num)#((num#num)#num))`;;

let candle_matan_series_input_narrow =
 `(((((0,1),9):(num#num)#num),(((1,0),9):(num#num)#num)):
    ((num#num)#num)#((num#num)#num))`;;

let candle_matan_series_prove_domain input =
  prove
   (mk_comb (`candle_q_interval_matan_series_domain`,input),
    REWRITE_TAC[candle_q_interval_matan_series_domain_def;
                candle_q_le_real; candle_q_nonzero_real;
                candle_q_matan_abs_upper_real;
                candle_q_matan_value_r2_real;
                candle_q_matan_derivative_r2_real;
                candle_q_matan_neg_one_fifth_real;
                candle_q_matan_nine_tenths_real;
                candle_q_real_def; candle_q_den_def;
                candle_lc_zreal_def; FST; SND] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_MAX_ACI] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV);;

let candle_matan_series_domain_symmetric =
  candle_matan_series_prove_domain candle_matan_series_input_symmetric;;

let candle_matan_series_domain_narrow =
  candle_matan_series_prove_domain candle_matan_series_input_narrow;;

let candle_matan_series_value_symmetric =
  let x = `x:real` in
  let membership =
    mk_comb
      (mk_comb (`candle_q_interval_contains`,
                candle_matan_series_input_symmetric),x) in
  let result =
    MATCH_MP
      (SPECL [candle_matan_series_input_symmetric;x]
        candle_q_interval_matan_series_sound)
      (CONJ candle_matan_series_domain_symmetric (ASSUME membership)) in
  GEN x (DISCH membership result);;

let candle_matan_series_derivative_symmetric =
  let x = `x:real` in
  let membership =
    mk_comb
      (mk_comb (`candle_q_interval_contains`,
                candle_matan_series_input_symmetric),x) in
  let result =
    MATCH_MP
      (SPECL [candle_matan_series_input_symmetric;x]
        candle_q_interval_dmatan_series_sound)
      (CONJ candle_matan_series_domain_symmetric (ASSUME membership)) in
  GEN x (DISCH membership result);;

let candle_matan_series_second_derivative_symmetric =
  let x = `x:real` in
  let membership =
    mk_comb
      (mk_comb (`candle_q_interval_contains`,
                candle_matan_series_input_symmetric),x) in
  let result =
    MATCH_MP
      (SPECL [candle_matan_series_input_symmetric;x]
        candle_q_interval_ddmatan_series_sound)
      (CONJ candle_matan_series_domain_symmetric (ASSUME membership)) in
  GEN x (DISCH membership result);;

let candle_matan_series_value_narrow =
  let x = `x:real` in
  let membership =
    mk_comb
      (mk_comb (`candle_q_interval_contains`,
                candle_matan_series_input_narrow),x) in
  let result =
    MATCH_MP
      (SPECL [candle_matan_series_input_narrow;x]
        candle_q_interval_matan_series_sound)
      (CONJ candle_matan_series_domain_narrow (ASSUME membership)) in
  GEN x (DISCH membership result);;

if hyp candle_matan_series_domain_symmetric <> [] ||
   hyp candle_matan_series_domain_narrow <> [] ||
   hyp candle_matan_series_value_symmetric <> [] ||
   hyp candle_matan_series_derivative_symmetric <> [] ||
   hyp candle_matan_series_second_derivative_symmetric <> [] ||
   hyp candle_matan_series_value_narrow <> [] then
  failwith "exact matan series: unexpected theorem assumptions";;

let candle_matan_series_test_axioms_after = axioms ();;
if length candle_matan_series_test_axioms_after <>
     length candle_matan_series_test_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_matan_series_test_axioms_before)
       candle_matan_series_test_axioms_after) then
  failwith "exact matan series: changed the global axiom set";;

let _ =
  print_endline
    "CANDLE_CV_EXACT_INTERVAL_MATAN_SERIES_RESULT fixtures=2 value=2 derivative=1 second_derivative=1";;

let _ = print_endline "CANDLE_CV_EXACT_INTERVAL_MATAN_SERIES_OK";;
