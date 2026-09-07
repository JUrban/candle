print_endline ("CANDLE_REFERENCE_SESSION_V1\t3d201321eda2675eb568432c83c2c604785548be0c9b1c4f65ec8bf720ac6e9f");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/arithmetic_geometric_mean.ml";;
candle_s1_emit_fingerprint "AGM" AGM;;
candle_s1_emit_fingerprint "AGM_ROOT" AGM_ROOT;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t3d201321eda2675eb568432c83c2c604785548be0c9b1c4f65ec8bf720ac6e9f");;
exit 0;;
