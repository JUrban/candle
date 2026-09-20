needs "candle/compute.ml";;
needs "candle/cv_compute_native_float_core.ml";;

open Candle_cv_native_float_core;;

let candle_nf_test_fuel = `CONS 0 (CONS 0 (CONS 0 ([]:num list)))`;;
let candle_nf_test_fuel_rep =
  REWRITE_CONV[candle_nf_fuel_def]
    (mk_comb (`candle_nf_fuel`,candle_nf_test_fuel));;

let candle_nf_test_lo =
  compute candle_cv_nf_round_compute_eqs
    (list_mk_comb
      (`candle_cv_nf_round_lo`,
       [`Cexp_num 100`; `Cexp_num 10000`;
        rand (concl candle_nf_test_fuel_rep);
        `Cexp_num 1234567`; `Cexp_num 8`]));;

let candle_nf_test_hi =
  compute candle_cv_nf_round_compute_eqs
    (list_mk_comb
      (`candle_cv_nf_round_hi`,
       [`Cexp_num 100`; `Cexp_num 10000`;
        rand (concl candle_nf_test_fuel_rep);
        `Cexp_num 1234567`; `Cexp_num 8`]));;

if hyp candle_nf_test_lo <> [] ||
   not (aconv (rand (concl candle_nf_test_lo))
              `Cexp_pair (Cexp_num 123) (Cexp_num 10)`)
then failwith "native-float lower rounding mismatch";;

if hyp candle_nf_test_hi <> [] ||
   not (aconv (rand (concl candle_nf_test_hi))
              `Cexp_pair (Cexp_num 124) (Cexp_num 10)`)
then failwith "native-float upper rounding mismatch";;

if hyp candle_cv_nf_round_lo_correct <> [] ||
   hyp candle_cv_nf_round_hi_correct <> [] ||
   hyp candle_nf_pair_roundtrip <> [] ||
   hyp candle_nf_round_lo_sound <> [] ||
   hyp candle_nf_round_hi_sound <> []
then failwith "native-float core theorem has assumptions";;

print_endline "CANDLE_CV_NATIVE_FLOAT_CORE_OK";;
