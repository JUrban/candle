needs "candle/compute.ml";;
needs "candle/cv_compute_native_float_batch.ml";;

open Candle_cv_native_float_core;;
open Candle_cv_native_float_polynomial;;
open Candle_cv_native_float_batch;;

let candle_nf_batch_test_fuel =
  `CONS 0 (CONS 0 (CONS 0 (CONS 0 (CONS 0 (CONS 0
    (CONS 0 (CONS 0 (CONS 0 (CONS 0 ([]:num list))))))))))`;;

let candle_nf_batch_test_sources =
 `[(17,
    [[2,8;101,10]; [3,8;103,11]; [5,9;107,11];
     [7,9;109,12]; [11,7;113,11]; [13,10;127,10]]);
   (16,
    [[2,5;2,6;131,7]; [3,5;2,6;137,8]; [3,5;3,7;139,8];
     [5,6;2,7;149,8]; [5,5;3,6;151,7]; [5,5;5,6;157,8]]);
   (18,
    [[7,5;2,7;163,8]; [7,6;3,7;167,8]; [7,5;5,6;173,7];
     [7,5;7,6;179,8]])]
   :(num#((num#num)list)list)list`;;

let candle_nf_batch_test_jobs =
 `[(17,
    [([2;101],[0]); ([3;103],[0;0]); ([5;107],[0;0;0]);
     ([7;109],[0;0;0;0]); ([11;113],[0]); ([13;127],[0;0;0])]);
   (16,
    [([2;2;131],[0;0]); ([3;2;137],[0;0;0]);
     ([3;3;139],[0;0;0;0]); ([5;2;149],[0;0;0;0;0]);
     ([5;3;151],[0;0]); ([5;5;157],[0;0;0])]);
   (18,
    [([7;2;163],[0;0]); ([7;3;167],[0;0;0]);
     ([7;5;173],[]); ([7;7;179],[0])])]
   :(num#(num list#num list)list)list`;;

let candle_nf_batch_test_alignment_tm =
  list_mk_comb
    (`candle_nf_fueled_batch_alignment`,
     [candle_nf_batch_test_sources;candle_nf_batch_test_jobs]);;

let candle_nf_batch_test_alignment_rewrite =
  REWRITE_CONV
    [candle_nf_fueled_batch_alignment_def;
     candle_nf_fueled_alignment_def; candle_nf_product_def;
     candle_nf_monomial_mantissa_def; candle_nf_monomial_exponent_def;
     FST; SND; LENGTH]
    candle_nf_batch_test_alignment_tm;;

let candle_nf_batch_test_alignment =
  EQT_ELIM
    (TRANS candle_nf_batch_test_alignment_rewrite
      (NUM_REDUCE_CONV
        (rand (concl candle_nf_batch_test_alignment_rewrite))));;

let candle_nf_batch_test_fuel_rep =
  REWRITE_CONV[candle_nf_fuel_def]
    (mk_comb (`candle_nf_fuel`,candle_nf_batch_test_fuel));;

let candle_nf_batch_test_jobs_rep =
  REWRITE_CONV
    [candle_nf_fueled_jobs_def; candle_nf_fueled_job_def;
     candle_nf_fueled_items_def; candle_nf_fueled_item_def;
     candle_nf_num_list_def; candle_nf_fuel_def; FST; SND]
    (mk_comb (`candle_nf_fueled_jobs`,candle_nf_batch_test_jobs));;

let candle_nf_batch_test_compute =
  compute candle_cv_nf_fueled_batch_compute_eqs
    (list_mk_comb
      (`candle_cv_nf_fueled_batch_round_hi`,
       [`Cexp_num 16`; `Cexp_num 65536`;
        rand (concl candle_nf_batch_test_fuel_rep);
        rand (concl candle_nf_batch_test_jobs_rep)]));;

let candle_nf_batch_test_correct =
  SPECL
    [candle_nf_batch_test_jobs;candle_nf_batch_test_fuel;
     `16`;`65536`]
    candle_cv_nf_fueled_batch_round_hi_correct;;

let candle_nf_batch_test_correct =
  PURE_REWRITE_RULE
    [candle_nf_batch_test_fuel_rep;candle_nf_batch_test_jobs_rep]
    candle_nf_batch_test_correct;;

let candle_nf_batch_test_represented =
  TRANS (SYM candle_nf_batch_test_correct) candle_nf_batch_test_compute;;

let candle_nf_batch_test_result =
  REWRITE_RULE[candle_nf_pairs_roundtrip;
               candle_nf_decode_pairs_def; candle_nf_decode_pair_def;
               candle_nf_decode_num_def]
    (AP_TERM `candle_nf_decode_pairs` candle_nf_batch_test_represented);;

let candle_nf_batch_test_sound =
  SPECL
    [candle_nf_batch_test_sources;candle_nf_batch_test_jobs;
     candle_nf_batch_test_fuel;`16`;`65536`]
    candle_nf_fueled_batch_round_hi_sound;;

let candle_nf_batch_test_sound =
  MP candle_nf_batch_test_sound
    (CONJ
      (EQT_ELIM (NUM_REDUCE_CONV `~(16 = 0)`))
      candle_nf_batch_test_alignment);;

let candle_nf_batch_test_sound =
  REWRITE_RULE[candle_nf_batch_test_result;candle_nf_batch_upper_def;
               FST;SND]
    candle_nf_batch_test_sound;;

if hyp candle_nf_batch_test_compute <> [] ||
   hyp candle_nf_batch_test_sound <> [] then
  failwith "batched native-float theorem has assumptions";;

if length (CONJUNCTS candle_nf_batch_test_sound) <> 3 then
  failwith "batched native-float theorem has wrong arity";;

print_endline "CANDLE_CV_NATIVE_FLOAT_BATCH_OK";;
