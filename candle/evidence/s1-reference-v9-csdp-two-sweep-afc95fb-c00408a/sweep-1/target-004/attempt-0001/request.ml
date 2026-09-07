print_endline ("CANDLE_REFERENCE_SESSION_V1\t3580116a4cc2cce21503cdc2a12707cce1b3337c916f407a9a28c7ed5ce980f9");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/bernoulli.ml";;
candle_s1_emit_fingerprint "SUM_OF_POWERS" SUM_OF_POWERS;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t3580116a4cc2cce21503cdc2a12707cce1b3337c916f407a9a28c7ed5ce980f9");;
exit 0;;
