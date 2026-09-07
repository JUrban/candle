print_endline ("CANDLE_REFERENCE_SESSION_V1\te0c007d9a72a886d23a9827ebca1d2bb9230c7b870d6ffc20993b5c85ef13734");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/lagrange.ml";;
candle_s1_emit_fingerprint "GROUP_LAGRANGE" GROUP_LAGRANGE;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\te0c007d9a72a886d23a9827ebca1d2bb9230c7b870d6ffc20993b5c85ef13734");;
exit 0;;
