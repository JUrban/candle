print_endline ("CANDLE_REFERENCE_SESSION_V1\t91bce2d15ae077fa4f6065565071a5411c45fe3f5497231f2937fd3061f13547");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/divharmonic.ml";;
candle_s1_emit_fingerprint "HARMONIC_DIVERGES" HARMONIC_DIVERGES;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t91bce2d15ae077fa4f6065565071a5411c45fe3f5497231f2937fd3061f13547");;
exit 0;;
