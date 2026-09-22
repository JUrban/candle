needs "candle/compute.ml";;
needs "candle/cv_compute_native_float_staged_sound.ml";;

let candle_nf_staged_sound_test_jobs =
 `CONS
    ((CONS ([0;0;0;0],(2,1))
       (CONS ([0;0;0;0],(3,2)) ([]:(num list#(num#num))list))),
     ([0;0;0;0],[0;0;0]))
    (CONS
      ((CONS ([0;0;0;0],(4,2)) ([]:(num list#(num#num))list)),
       ([0;0;0;0],[0]))
      ([]:(((num list#(num#num))list)#(num list#num list))list))`;;

let candle_nf_staged_sound_test_rep =
  REWRITE_CONV[candle_nf_staged_polynomial_jobs_def;
               candle_nf_staged_polynomial_job_def;
               candle_nf_staged_product_steps_def;
               candle_nf_staged_product_step_def;
               candle_nf_fuel_def; candle_nf_pair_def; FST; SND]
    (mk_comb (`candle_nf_staged_polynomial_jobs`,
      candle_nf_staged_sound_test_jobs));;

let candle_nf_staged_sound_test_valid_compute =
  compute candle_cv_nf_staged_validity_compute_eqs
    (list_mk_comb
      (`candle_cv_nf_staged_polynomial_valid`,
       [`Cexp_num 10`; `Cexp_num 0`; `Cexp_num 1000`;
        rand (concl candle_nf_staged_sound_test_rep);
        `Cexp_pair (Cexp_num 0) (Cexp_num 0)`]));;

let candle_nf_staged_sound_test_valid_correct =
  REWRITE_RULE
    [candle_nf_staged_sound_test_rep; candle_nf_pair_def; FST; SND]
    (SPECL
      [candle_nf_staged_sound_test_jobs; `10`; `0`; `1000`; `(0,0)`]
      candle_cv_nf_staged_polynomial_valid_correct);;

let candle_nf_staged_sound_test_valid_bridge =
  TRANS (SYM candle_nf_staged_sound_test_valid_correct)
    candle_nf_staged_sound_test_valid_compute;;

let candle_nf_staged_sound_test_valid =
  MATCH_MP candle_cv_nf_boolean_true
    candle_nf_staged_sound_test_valid_bridge;;

let candle_nf_staged_sound_test_theorem =
  MATCH_MP
    (SPECL
      [candle_nf_staged_sound_test_jobs; `10`; `0`; `1000`; `(0,0)`]
      candle_nf_staged_polynomial_scaled_sound)
    (CONJ (ARITH_RULE `~(10 = 0)`)
      candle_nf_staged_sound_test_valid);;

let candle_nf_staged_sound_test_result_compute =
  compute candle_cv_nf_staged_polynomial_compute_eqs
    (list_mk_comb
      (`candle_cv_nf_staged_polynomial`,
       [`Cexp_num 10`; `Cexp_num 0`; `Cexp_num 1000`;
        rand (concl candle_nf_staged_sound_test_rep);
        `Cexp_pair (Cexp_num 0) (Cexp_num 0)`]));;

let candle_nf_staged_sound_test_result_correct =
  REWRITE_RULE
    [candle_nf_staged_sound_test_rep; candle_nf_pair_def; FST; SND]
    (SPECL
      [candle_nf_staged_sound_test_jobs; `10`; `0`; `1000`; `(0,0)`]
      candle_cv_nf_staged_polynomial_correct);;

let candle_nf_staged_sound_test_result_bridge =
  TRANS (SYM candle_nf_staged_sound_test_result_correct)
    candle_nf_staged_sound_test_result_compute;;

if hyp candle_nf_staged_sound_test_valid_compute <> [] ||
   hyp candle_nf_staged_sound_test_valid <> [] ||
   hyp candle_nf_staged_sound_test_theorem <> [] ||
   hyp candle_nf_staged_sound_test_result_compute <> [] ||
   hyp candle_nf_staged_sound_test_result_bridge <> [] then
  failwith "staged soundness theorem has assumptions";;

if rand (concl candle_nf_staged_sound_test_valid_compute) <>
   `Cexp_num 1` then
  failwith "staged soundness validity mismatch";;

print_endline "CANDLE_CV_NATIVE_FLOAT_STAGED_SOUND_OK";;
