print_endline ("CANDLE_REFERENCE_SESSION_V1\t78a738f8f614d6a9ad7da46ab3c524b2482e11f85cff79fcfa369c7415b12363");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/perfect.ml";;
candle_s1_emit_fingerprint "PERFECT_EUCLID" PERFECT_EUCLID;;
candle_s1_emit_fingerprint "PERFECT_EULER" PERFECT_EULER;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t78a738f8f614d6a9ad7da46ab3c524b2482e11f85cff79fcfa369c7415b12363");;
exit 0;;
