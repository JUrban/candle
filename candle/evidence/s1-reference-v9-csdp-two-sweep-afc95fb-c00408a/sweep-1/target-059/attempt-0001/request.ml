print_endline ("CANDLE_REFERENCE_SESSION_V1\tcd5bb50aadd1be106df3f350a887ac64d6e7bcf6b18ea6e31c769d5b1bc296d9");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/stirling.ml";;
candle_s1_emit_fingerprint "STIRLING" STIRLING;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\tcd5bb50aadd1be106df3f350a887ac64d6e7bcf6b18ea6e31c769d5b1bc296d9");;
exit 0;;
