needs "candle/cv_compute_analytic_expr_fixed_scale_sound.ml";;

open Candle_cv_analytic_expr_fixed_scale_sound;;

let candle_cv_fs_sound_test =
  SPECL [`(7,2):num#num`; `(3,11):num#num`] candle_fs_add_real;;

let candle_cv_fs_floor_sound_test =
  MP
    (SPECL [`(2,7):num#num`; `3:num`] candle_fs_floor_div_sound)
    (ARITH_RULE `~((3:num) = 0)`);;

let candle_cv_fs_ceil_sound_test =
  MP
    (SPECL [`(11,3):num#num`; `7:num`] candle_fs_ceil_div_sound)
    (ARITH_RULE `~((7:num) = 0)`);;

let candle_cv_fs_to_q_sound_test =
  SPEC `(19,5):num#num` candle_fs_to_q_real;;

let candle_cv_fs_constant_sound_test =
  SPEC `((7,2),4):(num#num)#num`
    candle_fs_interval_constant_sound;;

let candle_cv_fs_add_sound_test =
  MP
    (SPECL
      [`candle_fs_interval_constant (((7,2),4):(num#num)#num)`;
       `candle_fs_interval_constant (((11,3),5):(num#num)#num)`;
       `candle_q_real (((7,2),4):(num#num)#num)`;
       `candle_q_real (((11,3),5):(num#num)#num)`]
      candle_fs_interval_add_sound)
    (CONJ
      (SPEC `((7,2),4):(num#num)#num`
        candle_fs_interval_constant_sound)
      (SPEC `((11,3),5):(num#num)#num`
        candle_fs_interval_constant_sound));;

let candle_cv_fs_mul_sound_test =
  MP
    (SPECL
      [`candle_fs_interval_constant (((7,2),4):(num#num)#num)`;
       `candle_fs_interval_constant (((11,3),5):(num#num)#num)`;
       `candle_q_real (((7,2),4):(num#num)#num)`;
       `candle_q_real (((11,3),5):(num#num)#num)`]
      candle_fs_interval_mul_sound)
    (CONJ
      (SPEC `((7,2),4):(num#num)#num`
        candle_fs_interval_constant_sound)
      (SPEC `((11,3),5):(num#num)#num`
        candle_fs_interval_constant_sound));;

if hyp candle_cv_fs_sound_test <> [] ||
   hyp candle_cv_fs_floor_sound_test <> [] ||
   hyp candle_cv_fs_ceil_sound_test <> [] ||
   hyp candle_cv_fs_to_q_sound_test <> [] ||
   hyp candle_cv_fs_constant_sound_test <> [] ||
   hyp candle_cv_fs_add_sound_test <> [] ||
   hyp candle_cv_fs_mul_sound_test <> [] ||
   hyp candle_fs_dot_abs_upper_sound <> [] ||
   hyp candle_fs_weighted_rows_abs_upper_sound <> [] then
  failwith "fixed-scale soundness substrate test has assumptions";;

print_endline "CANDLE_CV_ANALYTIC_EXPR_FIXED_SCALE_SOUND_OK";;
