print_endline ("CANDLE_REFERENCE_SESSION_V1\t07bfc7760aa4c3a0e0aeea1438ce3e8e0288177a47ac4e8fdee71464348f2b50");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/thales.ml";;
candle_s1_emit_fingerprint "THALES" THALES;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t07bfc7760aa4c3a0e0aeea1438ce3e8e0288177a47ac4e8fdee71464348f2b50");;
exit 0;;
