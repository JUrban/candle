print_endline ("CANDLE_REFERENCE_SESSION_V1\tfa69b50444bd064c12a728c5e0c948691f2823f0a4b00f7defc8175110651442");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/gcd.ml";;
candle_s1_emit_fingerprint "EGCD" EGCD;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\tfa69b50444bd064c12a728c5e0c948691f2823f0a4b00f7defc8175110651442");;
exit 0;;
