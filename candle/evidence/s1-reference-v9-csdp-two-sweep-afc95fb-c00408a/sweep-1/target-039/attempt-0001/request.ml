print_endline ("CANDLE_REFERENCE_SESSION_V1\td2c7e9c86b90dd91e7019b3e3e3eb989919839e00c52b4096187bdf75d51b851");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/lagrange.ml";;
candle_s1_emit_fingerprint "GROUP_LAGRANGE" GROUP_LAGRANGE;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\td2c7e9c86b90dd91e7019b3e3e3eb989919839e00c52b4096187bdf75d51b851");;
exit 0;;
