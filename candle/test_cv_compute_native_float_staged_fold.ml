needs "candle/compute.ml";;
needs "candle/cv_compute_native_float_staged_fold.ml";;

open Candle_cv_native_float_core;;
open Candle_cv_native_float_staged;;
open Candle_cv_native_float_staged_fold;;

let candle_nf_staged_fold_round_fuel =
  `CONS 0 (CONS 0 (CONS 0 (CONS 0 (CONS 0 (CONS 0
    (CONS 0 (CONS 0 ([]:num list))))))))`;;

let candle_nf_staged_fold_product_steps =
 `CONS
    ([0;0;0;0;0;0;0;0],(12345,5))
    (CONS ([0;0;0;0;0;0;0;0],(6789,4))
      ([]:(num list#(num#num))list))`;;

let candle_nf_staged_fold_product_rep =
  REWRITE_CONV[candle_nf_staged_product_steps_def;
               candle_nf_staged_product_step_def;
               candle_nf_fuel_def; candle_nf_pair_def; FST; SND]
    (mk_comb (`candle_nf_staged_product_steps`,
      candle_nf_staged_fold_product_steps));;

let candle_nf_staged_fold_product_compute =
  compute candle_cv_nf_staged_fold_compute_eqs
    (list_mk_comb
      (`candle_cv_nf_staged_product`,
       [`Cexp_num 10`; `Cexp_num 0`; `Cexp_num 1000`;
        rand (concl candle_nf_staged_fold_product_rep);
        `Cexp_pair (Cexp_num 1) (Cexp_num 0)`]));;

let candle_nf_staged_fold_product_correct =
  SPECL
    [candle_nf_staged_fold_product_steps; `10`; `0`; `1000`; `(1,0)`]
    candle_cv_nf_staged_product_correct;;

let candle_nf_staged_fold_product_valid =
  prove
   (`candle_nf_staged_product_valid 10 0 1000
      [( [0;0;0;0;0;0;0;0],(12345,5));
       ( [0;0;0;0;0;0;0;0],(6789,4))] (1,0)`,
    REWRITE_TAC[candle_nf_staged_product_valid_def;
                candle_nf_scaled_mul_round_hi_def;
                candle_nf_round_hi_def; FST; SND] THEN
    NUM_REDUCE_TAC);;

let candle_nf_staged_fold_product_sound =
  MP
    (SPECL
      [candle_nf_staged_fold_product_steps; `10`; `0`; `1000`; `(1,0)`]
      candle_nf_staged_product_sound)
    (CONJ (EQT_ELIM (NUM_REDUCE_CONV `~(10 = 0)`))
      candle_nf_staged_fold_product_valid);;

let candle_nf_staged_fold_sum_steps =
 `CONS
    ([0;0;0;0;0;0;0;0],([0],(2,1)))
    (CONS ([0;0;0;0;0;0;0;0],([0;0],(3,2)))
      ([]:(num list#(num list#(num#num)))list))`;;

let candle_nf_staged_fold_sum_rep =
  REWRITE_CONV[candle_nf_staged_sum_steps_def;
               candle_nf_staged_sum_step_def;
               candle_nf_fuel_def; candle_nf_pair_def; FST; SND]
    (mk_comb (`candle_nf_staged_sum_steps`,
      candle_nf_staged_fold_sum_steps));;

let candle_nf_staged_fold_sum_compute =
  compute candle_cv_nf_staged_fold_compute_eqs
    (list_mk_comb
      (`candle_cv_nf_staged_sum`,
       [`Cexp_num 10`; `Cexp_num 1000`;
        rand (concl candle_nf_staged_fold_sum_rep);
        `Cexp_pair (Cexp_num 0) (Cexp_num 0)`]));;

let candle_nf_staged_fold_sum_correct =
  SPECL
    [candle_nf_staged_fold_sum_steps; `10`; `1000`; `(0,0)`]
    candle_cv_nf_staged_sum_correct;;

let candle_nf_staged_fold_sum_valid =
  prove
   (`candle_nf_staged_sum_valid 10 1000
      [([0;0;0;0;0;0;0;0],([0],(2,1)));
       ([0;0;0;0;0;0;0;0],([0;0],(3,2)))] (0,0)`,
    REWRITE_TAC[candle_nf_staged_sum_valid_def;
                candle_nf_add_power_complete_def;
                candle_nf_add_round_hi_def; candle_nf_add_raw_def;
                candle_nf_power_fuel_def; candle_nf_round_hi_def;
                LENGTH; FST; SND] THEN
    NUM_REDUCE_TAC);;

let candle_nf_staged_fold_sum_sound =
  MP
    (SPECL
      [candle_nf_staged_fold_sum_steps; `10`; `1000`; `(0,0)`]
      candle_nf_staged_sum_sound)
    (CONJ (EQT_ELIM (NUM_REDUCE_CONV `~(10 = 0)`))
      candle_nf_staged_fold_sum_valid);;

if hyp candle_nf_staged_fold_product_compute <> [] ||
   hyp candle_nf_staged_fold_product_correct <> [] ||
   hyp candle_nf_staged_fold_product_sound <> [] ||
   hyp candle_nf_staged_fold_sum_compute <> [] ||
   hyp candle_nf_staged_fold_sum_correct <> [] ||
   hyp candle_nf_staged_fold_sum_sound <> []
then failwith "staged fold theorem has assumptions";;

print_endline "CANDLE_CV_NATIVE_FLOAT_STAGED_FOLD_OK";;
