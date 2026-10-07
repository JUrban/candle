needs "candle/cv_compute_analytic_expr_fixed_scale_angle_polynomials_sound.ml";;

open Candle_cv_analytic_expr_fixed_scale_angle_polynomials_sound;;

let _ =
  let theorems =
    [candle_cv_fs_angle_interval_sum_correct;
     candle_cv_fs_angle_delta_value_correct;
     candle_cv_fs_angle_delta_gradient_correct;
     candle_cv_fs_angle_delta_hessian_correct;
     candle_cv_fs_angle_q_hessian_correct;
     candle_cv_fs_angle_q_delta_hessian_correct;
     candle_cv_fs_angle_four_x0_delta_correct;
     candle_cv_fs_angle_four_x0_delta_q_correct] in
  if List.exists (fun theorem -> hyp theorem <> []) theorems then
    failwith "fixed-scale angle representation: assumptions";
  print_endline
    "CANDLE_CV_FIXED_SCALE_ANGLE_POLYNOMIALS_SOUND_OK assumptions=0";;
