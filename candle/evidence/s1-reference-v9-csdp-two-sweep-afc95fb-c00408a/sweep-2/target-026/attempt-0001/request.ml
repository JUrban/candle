print_endline ("CANDLE_REFERENCE_SESSION_V1\t8718cad35e06d2e90df44c7da831e9e3d2a07684b13a7fe57eb55efa4f783650");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/feuerbach.ml";;
candle_s1_emit_fingerprint "FEUERBACH" FEUERBACH;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t8718cad35e06d2e90df44c7da831e9e3d2a07684b13a7fe57eb55efa4f783650");;
exit 0;;
