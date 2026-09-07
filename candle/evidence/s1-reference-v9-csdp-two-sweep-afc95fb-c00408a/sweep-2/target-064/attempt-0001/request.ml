print_endline ("CANDLE_REFERENCE_SESSION_V1\t6a8070d3379ee98da0990c835c9aac4c0dec7b408ddb6d1756d45bb58f64aabb");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/two_squares.ml";;
candle_s1_emit_fingerprint "SUM_OF_TWO_SQUARES" SUM_OF_TWO_SQUARES;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t6a8070d3379ee98da0990c835c9aac4c0dec7b408ddb6d1756d45bb58f64aabb");;
exit 0;;
