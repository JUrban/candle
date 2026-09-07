print_endline ("CANDLE_REFERENCE_SESSION_V1\t945826c5f9c43c9e0528ca0100a9eef30308e47192bdbc252405f0de5f391396");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/triangular.ml";;
candle_s1_emit_fingerprint "TRIANGLE_FINITE_SUM" TRIANGLE_FINITE_SUM;;
candle_s1_emit_fingerprint "TRIANGLE_CONVERGES'" TRIANGLE_CONVERGES';;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t945826c5f9c43c9e0528ca0100a9eef30308e47192bdbc252405f0de5f391396");;
exit 0;;
