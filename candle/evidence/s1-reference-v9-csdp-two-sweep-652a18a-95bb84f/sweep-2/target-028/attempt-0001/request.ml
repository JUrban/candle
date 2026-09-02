print_endline ("CANDLE_REFERENCE_SESSION_V1\t56bbb784c9f11dcfaaa52fa7125671d6a6f766570928b875fe243a76965aa113");;
loadt "/project/worktrees/candle-reference-v9-launch-652a18a/candle/fingerprint.ml";;
loadt "100/four_squares.ml";;
candle_s1_emit_fingerprint "SUM_OF_TWO_SQUARES" SUM_OF_TWO_SQUARES;;
candle_s1_emit_fingerprint "LAGRANGE_NUM" LAGRANGE_NUM;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t56bbb784c9f11dcfaaa52fa7125671d6a6f766570928b875fe243a76965aa113");;
exit 0;;
