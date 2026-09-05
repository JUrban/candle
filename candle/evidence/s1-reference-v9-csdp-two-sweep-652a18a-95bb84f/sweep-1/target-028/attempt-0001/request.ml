print_endline ("CANDLE_REFERENCE_SESSION_V1\t39315a71e89680d8df40fe690d0ade0b9137c2a83afef94d652561b35fc0a39b");;
loadt "/project/worktrees/candle-reference-v9-launch-652a18a/candle/fingerprint.ml";;
loadt "100/four_squares.ml";;
candle_s1_emit_fingerprint "SUM_OF_TWO_SQUARES" SUM_OF_TWO_SQUARES;;
candle_s1_emit_fingerprint "LAGRANGE_NUM" LAGRANGE_NUM;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t39315a71e89680d8df40fe690d0ade0b9137c2a83afef94d652561b35fc0a39b");;
exit 0;;
