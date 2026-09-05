print_endline ("CANDLE_REFERENCE_SESSION_V1\td0701a7b251a1e0a616915e67e35bf79c6e38e73fb9b3a5da6abcde860cf348a");;
loadt "/project/worktrees/candle-reference-v9-launch-652a18a/candle/fingerprint.ml";;
loadt "100/arithmetic_geometric_mean.ml";;
candle_s1_emit_fingerprint "AGM" AGM;;
candle_s1_emit_fingerprint "AGM_ROOT" AGM_ROOT;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\td0701a7b251a1e0a616915e67e35bf79c6e38e73fb9b3a5da6abcde860cf348a");;
exit 0;;
