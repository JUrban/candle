print_endline ("CANDLE_REFERENCE_SESSION_V1\t353280d379f9938a65cc3737701d7fe42654eb22a4065bf6a38b599817ce2730");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/four_squares.ml";;
candle_s1_emit_fingerprint "SUM_OF_TWO_SQUARES" SUM_OF_TWO_SQUARES;;
candle_s1_emit_fingerprint "LAGRANGE_NUM" LAGRANGE_NUM;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t353280d379f9938a65cc3737701d7fe42654eb22a4065bf6a38b599817ce2730");;
exit 0;;
