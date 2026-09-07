print_endline ("CANDLE_REFERENCE_SESSION_V1\tf882d3ff6474eac01ce354139bcee67da88186fffe83125c3be95d96992c5b96");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/four_squares.ml";;
candle_s1_emit_fingerprint "SUM_OF_TWO_SQUARES" SUM_OF_TWO_SQUARES;;
candle_s1_emit_fingerprint "LAGRANGE_NUM" LAGRANGE_NUM;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\tf882d3ff6474eac01ce354139bcee67da88186fffe83125c3be95d96992c5b96");;
exit 0;;
