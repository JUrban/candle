print_endline ("CANDLE_REFERENCE_SESSION_V1\t9a54ea171d035500588885a5689e06512ffcbe13537608c97ccbb5bdad4c353a");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/fta.ml";;
candle_s1_emit_fingerprint "FTA" FTA;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t9a54ea171d035500588885a5689e06512ffcbe13537608c97ccbb5bdad4c353a");;
exit 0;;
