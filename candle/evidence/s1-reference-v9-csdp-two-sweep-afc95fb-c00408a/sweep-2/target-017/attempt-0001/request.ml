print_endline ("CANDLE_REFERENCE_SESSION_V1\tba6076579703d82f35fec7cf6137650877cbb2255aba1530a9de4c7a76dafca8");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/cubic.ml";;
candle_s1_emit_fingerprint "CUBIC" CUBIC;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\tba6076579703d82f35fec7cf6137650877cbb2255aba1530a9de4c7a76dafca8");;
exit 0;;
