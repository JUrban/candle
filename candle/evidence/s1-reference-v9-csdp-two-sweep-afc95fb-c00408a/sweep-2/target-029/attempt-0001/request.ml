print_endline ("CANDLE_REFERENCE_SESSION_V1\t5cbd19bc0e5df45b4cc76fcb5b889f2ac54bab0b714afa745328b7a5099572b6");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/friendship.ml";;
candle_s1_emit_fingerprint "FRIENDSHIP" FRIENDSHIP;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t5cbd19bc0e5df45b4cc76fcb5b889f2ac54bab0b714afa745328b7a5099572b6");;
exit 0;;
