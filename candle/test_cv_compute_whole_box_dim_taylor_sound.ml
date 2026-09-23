needs "candle/compute.ml";;
needs "candle/cv_compute_whole_box_dim_taylor_sound.ml";;

open Candle_cv_whole_box_dim_taylor_sound;;

if hyp candle_q_dim_real_zero <> [] ||
   hyp candle_q_center_environment_list_contains <> [] ||
   hyp candle_q_center_environment_list_length <> [] ||
   hyp candle_q_radius_list_length <> [] ||
   hyp candle_q_radius_list_nonnegative <> [] ||
   hyp candle_q_dot_abs_upper_sound <> [] then
  failwith "dimension-generic Taylor semantic invariant assumptions mismatch";;

print_endline "CANDLE_CV_WHOLE_BOX_DIM_TAYLOR_SOUND_OK";;
