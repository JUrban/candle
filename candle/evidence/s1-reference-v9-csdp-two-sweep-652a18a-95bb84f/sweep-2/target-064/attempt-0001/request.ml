print_endline ("CANDLE_REFERENCE_SESSION_V1\t5e91d41817ed52443660635dbfab0ef01224287ec46730cb7133b972a291f2c2");;
loadt "/project/worktrees/candle-reference-v9-launch-652a18a/candle/fingerprint.ml";;
loadt "100/two_squares.ml";;
candle_s1_emit_fingerprint "SUM_OF_TWO_SQUARES" SUM_OF_TWO_SQUARES;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t5e91d41817ed52443660635dbfab0ef01224287ec46730cb7133b972a291f2c2");;
exit 0;;
