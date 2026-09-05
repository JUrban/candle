print_endline ("CANDLE_REFERENCE_SESSION_V1\t60a090e811bf83b4be46d307adb11fbc59eab0055bbde2e52bfad60bcdd784d9");;
loadt "/project/worktrees/candle-reference-v9-launch-652a18a/candle/fingerprint.ml";;
loadt "100/triangular.ml";;
candle_s1_emit_fingerprint "TRIANGLE_FINITE_SUM" TRIANGLE_FINITE_SUM;;
candle_s1_emit_fingerprint "TRIANGLE_CONVERGES'" TRIANGLE_CONVERGES';;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t60a090e811bf83b4be46d307adb11fbc59eab0055bbde2e52bfad60bcdd784d9");;
exit 0;;
