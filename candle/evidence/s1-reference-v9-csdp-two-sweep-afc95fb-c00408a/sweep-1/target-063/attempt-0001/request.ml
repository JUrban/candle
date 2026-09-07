print_endline ("CANDLE_REFERENCE_SESSION_V1\t989bdfcec421d8ee40e9e97a5a9693350021e098afd721d032aa22c66a00e982");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/triangular.ml";;
candle_s1_emit_fingerprint "TRIANGLE_FINITE_SUM" TRIANGLE_FINITE_SUM;;
candle_s1_emit_fingerprint "TRIANGLE_CONVERGES'" TRIANGLE_CONVERGES';;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t989bdfcec421d8ee40e9e97a5a9693350021e098afd721d032aa22c66a00e982");;
exit 0;;
