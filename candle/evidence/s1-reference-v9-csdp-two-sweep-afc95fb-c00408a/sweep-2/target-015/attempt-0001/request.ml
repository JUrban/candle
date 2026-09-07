print_endline ("CANDLE_REFERENCE_SESSION_V1\ted1aaa1c723a42b3162c1adb6ee1a31814dbc2809408091ed36bd17b92878043");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/cosine.ml";;
candle_s1_emit_fingerprint "LAW_OF_COSINES" LAW_OF_COSINES;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\ted1aaa1c723a42b3162c1adb6ee1a31814dbc2809408091ed36bd17b92878043");;
exit 0;;
