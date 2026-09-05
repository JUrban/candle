print_endline ("CANDLE_REFERENCE_SESSION_V1\tc7fde31724332deaaa601e4bead9d67bb36b4bd6f253fc1a2c18cb5bac1b62af");;
loadt "/project/worktrees/candle-reference-v9-launch-652a18a/candle/fingerprint.ml";;
loadt "100/gcd.ml";;
candle_s1_emit_fingerprint "EGCD" EGCD;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\tc7fde31724332deaaa601e4bead9d67bb36b4bd6f253fc1a2c18cb5bac1b62af");;
exit 0;;
