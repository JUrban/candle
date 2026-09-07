print_endline ("CANDLE_REFERENCE_SESSION_V1\td605f3d04f7905721a64f3c9002bff8ddcee66877607ac04042f03f43aec951d");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/birthday.ml";;
candle_s1_emit_fingerprint "BIRTHDAY_THM" BIRTHDAY_THM;;
candle_s1_emit_fingerprint "BIRTHDAY_THM_EXPLICIT" BIRTHDAY_THM_EXPLICIT;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\td605f3d04f7905721a64f3c9002bff8ddcee66877607ac04042f03f43aec951d");;
exit 0;;
