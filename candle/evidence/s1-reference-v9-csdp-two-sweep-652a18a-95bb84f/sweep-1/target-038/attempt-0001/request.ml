print_endline ("CANDLE_REFERENCE_SESSION_V1\te9ec52501bcc992f4f0802d22032304b368f7cbcc6be43f53680f1aac5fa491d");;
loadt "/project/worktrees/candle-reference-v9-launch-652a18a/candle/fingerprint.ml";;
loadt "100/konigsberg.ml";;
candle_s1_emit_fingerprint "KOENIGSBERG" KOENIGSBERG;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\te9ec52501bcc992f4f0802d22032304b368f7cbcc6be43f53680f1aac5fa491d");;
exit 0;;
