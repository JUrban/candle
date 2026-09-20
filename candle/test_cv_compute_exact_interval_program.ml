needs "candle/compute.ml";;
needs "candle/cv_compute_exact_interval_program.ml";;

open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_mul_core;;
open Candle_cv_exact_interval_program;;

let candle_cv_q_program_test_env =
 `[(((((1,0),0),((2,0),0)):
       ((num#num)#num)#((num#num)#num)));
    ((((3,0),0),((5,0),0)):
       ((num#num)#num)#((num#num)#num))]`;;

let candle_cv_q_program_test_program =
 `[Candle_q_load 0; Candle_q_load 1; Candle_q_mul;
   Candle_q_push 3 0 1; Candle_q_neg; Candle_q_add]`;;

let candle_cv_q_program_test_expected =
 `[((((6,3),1),((20,3),1)):
     ((num#num)#num)#((num#num)#num))]`;;

let candle_cv_q_program_test_env_rep =
  REWRITE_CONV[candle_cv_q_interval_list_def; candle_cv_q_interval_def;
               candle_cv_q_def; candle_cv_lc_z_def]
    (mk_comb (`candle_cv_q_interval_list`,candle_cv_q_program_test_env));;

let candle_cv_q_program_test_program_rep =
  REWRITE_CONV[candle_cv_q_instruction_list_def;
               candle_cv_q_instruction_def; candle_cv_q_def;
               candle_cv_lc_z_def]
    (mk_comb
      (`candle_cv_q_instruction_list`,candle_cv_q_program_test_program));;

let candle_cv_q_program_test_empty_rep =
  REWRITE_CONV[candle_cv_q_interval_list_def]
    `candle_cv_q_interval_list []`;;

let candle_cv_q_program_test_expected_rep =
  REWRITE_CONV[candle_cv_q_interval_list_def; candle_cv_q_interval_def;
               candle_cv_q_def; candle_cv_lc_z_def]
    (mk_comb
      (`candle_cv_q_interval_list`,candle_cv_q_program_test_expected));;

let candle_cv_q_program_test_th =
  compute candle_cv_q_interval_program_compute_eqs
    (mk_comb
      (mk_comb
        (mk_comb (`candle_cv_q_interval_run`,
          rand (concl candle_cv_q_program_test_env_rep)),
          rand (concl candle_cv_q_program_test_program_rep)),
        rand (concl candle_cv_q_program_test_empty_rep)));;

if hyp candle_cv_q_program_test_th <> [] ||
   not (aconv (rand (concl candle_cv_q_program_test_th))
              (rand (concl candle_cv_q_program_test_expected_rep)))
then failwith "exact interval postfix program compute mismatch";;

let candle_cv_q_program_test_real =
 `candle_q_real_run [&1;&3]
    [Candle_q_load 0; Candle_q_load 1; Candle_q_mul;
     Candle_q_push 3 0 1; Candle_q_neg; Candle_q_add] [] = [&3 / &2]`;;

let candle_cv_q_program_test_real_th =
  prove
   (candle_cv_q_program_test_real,
    REWRITE_TAC[ONE; candle_q_real_run_def; candle_q_real_step_def;
                candle_q_real_lookup_def; candle_q_real_head_def;
                candle_q_real_tail_def; candle_q_real_def;
                candle_q_den_def;
                Candle_cv_linear_combination_realize.candle_lc_zreal_def] THEN
    REWRITE_TAC[CONS_11] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV);;

if hyp candle_q_interval_step_sound <> [] ||
   hyp candle_q_interval_run_sound <> [] ||
   hyp candle_cv_q_interval_step_correct <> [] ||
   hyp candle_cv_q_interval_run_correct <> [] ||
   hyp candle_cv_q_program_test_real_th <> []
then failwith "exact interval postfix theorem has assumptions";;

print_endline "CANDLE_CV_EXACT_INTERVAL_PROGRAM_OK";;
