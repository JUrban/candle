print_endline ("CANDLE_REFERENCE_SESSION_V1\ta52ed6a044e06f9a2d9383237190c75d28bf121ec49e3d20e96ae8f9df054a78");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/wilson.ml";;
candle_s1_emit_fingerprint "WILSON" WILSON;;
candle_s1_emit_fingerprint "WILSON_EQ" WILSON_EQ;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\ta52ed6a044e06f9a2d9383237190c75d28bf121ec49e3d20e96ae8f9df054a78");;
exit 0;;
