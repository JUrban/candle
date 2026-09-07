print_endline ("CANDLE_REFERENCE_SESSION_V1\t6deba2b7ad089615781a8ba83b3a146154b974253bff9b7daebb686d1815ae86");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/leibniz.ml";;
candle_s1_emit_fingerprint "LEIBNIZ_PI" LEIBNIZ_PI;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t6deba2b7ad089615781a8ba83b3a146154b974253bff9b7daebb686d1815ae86");;
exit 0;;
