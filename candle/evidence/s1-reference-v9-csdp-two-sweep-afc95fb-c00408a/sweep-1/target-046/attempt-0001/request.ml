print_endline ("CANDLE_REFERENCE_SESSION_V1\te0b48f94ce06283ad6a1fc485edd70e000addc86a5bf13eb1b6dd6fe8a176c9e");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/perfect.ml";;
candle_s1_emit_fingerprint "PERFECT_EUCLID" PERFECT_EUCLID;;
candle_s1_emit_fingerprint "PERFECT_EULER" PERFECT_EULER;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\te0b48f94ce06283ad6a1fc485edd70e000addc86a5bf13eb1b6dd6fe8a176c9e");;
exit 0;;
