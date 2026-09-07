print_endline ("CANDLE_REFERENCE_SESSION_V1\t450921b69c9410cae1bb74c97dfaf670fa9c10cf9c3647b7c1c6b94d208b77f2");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/two_squares.ml";;
candle_s1_emit_fingerprint "SUM_OF_TWO_SQUARES" SUM_OF_TWO_SQUARES;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t450921b69c9410cae1bb74c97dfaf670fa9c10cf9c3647b7c1c6b94d208b77f2");;
exit 0;;
