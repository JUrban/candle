print_endline ("CANDLE_REFERENCE_SESSION_V1\t3d2876f2a0a38dca1302e1c8f51fa287ae55d9804f39b0e8f094176e81d4ecae");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/cubic.ml";;
candle_s1_emit_fingerprint "CUBIC" CUBIC;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t3d2876f2a0a38dca1302e1c8f51fa287ae55d9804f39b0e8f094176e81d4ecae");;
exit 0;;
