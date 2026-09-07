print_endline ("CANDLE_REFERENCE_SESSION_V1\t66b908a2048de22303d36ea8e1e96bb36cf4656b6084e5b3ca2ca11f654a7464");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/fta.ml";;
candle_s1_emit_fingerprint "FTA" FTA;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t66b908a2048de22303d36ea8e1e96bb36cf4656b6084e5b3ca2ca11f654a7464");;
exit 0;;
