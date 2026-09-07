print_endline ("CANDLE_REFERENCE_SESSION_V1\td5993ce5baccd29cdbe359861ceac1080b8cd15a4242406c86f9bf879018f26c");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/desargues.ml";;
candle_s1_emit_fingerprint "DESARGUES_DIRECT" DESARGUES_DIRECT;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\td5993ce5baccd29cdbe359861ceac1080b8cd15a4242406c86f9bf879018f26c");;
exit 0;;
