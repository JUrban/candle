print_endline ("CANDLE_REFERENCE_SESSION_V1\ta4eef299147fb429a6d73ad7631b45d0442d8128dec4b7a7c2f432be1bea5008");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/desargues.ml";;
candle_s1_emit_fingerprint "DESARGUES_DIRECT" DESARGUES_DIRECT;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\ta4eef299147fb429a6d73ad7631b45d0442d8128dec4b7a7c2f432be1bea5008");;
exit 0;;
