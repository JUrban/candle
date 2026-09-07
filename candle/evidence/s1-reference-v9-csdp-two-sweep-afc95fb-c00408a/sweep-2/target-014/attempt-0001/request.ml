print_endline ("CANDLE_REFERENCE_SESSION_V1\t3f11c967bb6c255069856024714a75184cf8efe7cc2f19abd5860859527b5616");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/constructible.ml";;
candle_s1_emit_fingerprint "DOUBLE_THE_CUBE" DOUBLE_THE_CUBE;;
candle_s1_emit_fingerprint "TRISECT_60_DEGREES" TRISECT_60_DEGREES;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t3f11c967bb6c255069856024714a75184cf8efe7cc2f19abd5860859527b5616");;
exit 0;;
