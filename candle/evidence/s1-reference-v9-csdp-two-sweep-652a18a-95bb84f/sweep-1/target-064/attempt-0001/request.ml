print_endline ("CANDLE_REFERENCE_SESSION_V1\tc52cf378a557e67c48e3a8303539de1995a0f266cbbc5958674d8ca052d324c4");;
loadt "/project/worktrees/candle-reference-v9-launch-652a18a/candle/fingerprint.ml";;
loadt "100/two_squares.ml";;
candle_s1_emit_fingerprint "SUM_OF_TWO_SQUARES" SUM_OF_TWO_SQUARES;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\tc52cf378a557e67c48e3a8303539de1995a0f266cbbc5958674d8ca052d324c4");;
exit 0;;
