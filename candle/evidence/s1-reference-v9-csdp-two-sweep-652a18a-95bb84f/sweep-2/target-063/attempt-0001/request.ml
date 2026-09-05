print_endline ("CANDLE_REFERENCE_SESSION_V1\teb709e6c29e8b43110ad874bedc00f9a626bbef511c1bda0820b477b47539059");;
loadt "/project/worktrees/candle-reference-v9-launch-652a18a/candle/fingerprint.ml";;
loadt "100/triangular.ml";;
candle_s1_emit_fingerprint "TRIANGLE_FINITE_SUM" TRIANGLE_FINITE_SUM;;
candle_s1_emit_fingerprint "TRIANGLE_CONVERGES'" TRIANGLE_CONVERGES';;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\teb709e6c29e8b43110ad874bedc00f9a626bbef511c1bda0820b477b47539059");;
exit 0;;
