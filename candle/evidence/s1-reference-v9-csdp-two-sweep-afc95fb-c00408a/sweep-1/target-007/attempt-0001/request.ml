print_endline ("CANDLE_REFERENCE_SESSION_V1\tec6e37587e504484f64a1fcce4e5a1453163d2a01f97115fc5affb7e58205af7");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/buffon.ml";;
candle_s1_emit_fingerprint "BUFFON_GENERAL" BUFFON_GENERAL;;
candle_s1_emit_fingerprint "BUFFON_SHORT" BUFFON_SHORT;;
candle_s1_emit_fingerprint "BUFFON_LONG" BUFFON_LONG;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\tec6e37587e504484f64a1fcce4e5a1453163d2a01f97115fc5affb7e58205af7");;
exit 0;;
