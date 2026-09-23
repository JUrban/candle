needs "candle/compute.ml";;
needs "candle/cv_compute_whole_box_jet_sound.ml";;

open Candle_cv_whole_box_jet_sound;;

if hyp candle_real_taylor_upper_mono <> [] then
  failwith "real Taylor monotonicity theorem assumptions mismatch";;

if hyp candle_q_jet_whole_box_upper_sound <> [] then
  failwith "whole-box upper soundness theorem assumptions mismatch";;

if hyp candle_q_jet_whole_box_accept_sound <> [] then
  failwith "whole-box acceptance soundness theorem assumptions mismatch";;

print_endline "CANDLE_CV_WHOLE_BOX_JET_SOUND_OK";;
