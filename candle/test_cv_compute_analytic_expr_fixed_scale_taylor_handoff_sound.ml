needs "candle/cv_compute_analytic_expr_fixed_scale_taylor_handoff_sound.ml";;

open Candle_cv_analytic_expr_fixed_scale_taylor_handoff_sound;;

let candle_matan_fs_handoff_sound_axioms_before = axioms ();;

if hyp candle_cv_matan_fs_q_upper_correct <> [] ||
   hyp candle_cv_matan_fs_q_abs_upper_correct <> [] ||
   hyp candle_cv_matan_fs_weighted_rows_upper_correct <> [] ||
   hyp candle_matan_fs_q_upper_sound <> [] ||
   hyp candle_matan_fs_q_abs_upper_sound <> [] ||
   hyp candle_matan_fs_weighted_rows_upper_sound <> [] ||
   hyp candle_matan_fs_half_ceil_sound <> [] ||
   hyp candle_matan_fs_integer_cast_negative <> [] ||
   hyp candle_matan_fs_integer_negative <> [] ||
   hyp candle_matan_fs_taylor_accept_sound <> [] then
  failwith "fixed-scale Taylor handoff scalar soundness assumptions";;

let candle_matan_fs_handoff_sound_axioms_after = axioms ();;
if length candle_matan_fs_handoff_sound_axioms_after <>
     length candle_matan_fs_handoff_sound_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_matan_fs_handoff_sound_axioms_before)
       candle_matan_fs_handoff_sound_axioms_after) then
  failwith "fixed-scale Taylor handoff scalar soundness axiom growth";;

print_endline
  "CANDLE_CV_MATAN_FS_HANDOFF_SCALAR_SOUND_RESULT correctness=3 soundness=7 assumptions=0 axiom_growth=0";;
print_endline "CANDLE_CV_MATAN_FS_HANDOFF_SCALAR_SOUND_OK";;
