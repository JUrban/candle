print_endline ("CANDLE_REFERENCE_SESSION_V1\tb6d7f8f9ca4ee2db3153c825826c0b4fc73bf098744fa77829ce9356ddb520b5");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/ramsey.ml";;
candle_s1_emit_fingerprint "RAMSEY" RAMSEY;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\tb6d7f8f9ca4ee2db3153c825826c0b4fc73bf098744fa77829ce9356ddb520b5");;
exit 0;;
