print_endline ("CANDLE_REFERENCE_SESSION_V1\te42ea0a7f0d8e8089b12ca87c3d3709e8d372f202a11bd516c0354c42be453cd");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/chords.ml";;
candle_s1_emit_fingerprint "SEGMENT_CHORDS" SEGMENT_CHORDS;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\te42ea0a7f0d8e8089b12ca87c3d3709e8d372f202a11bd516c0354c42be453cd");;
exit 0;;
