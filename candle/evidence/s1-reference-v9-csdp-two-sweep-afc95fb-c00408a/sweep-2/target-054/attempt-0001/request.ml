print_endline ("CANDLE_REFERENCE_SESSION_V1\tc8a606f4444ccf303d65289b0e6a3724f8b96b6c92188cc585d9c2bf22b78a3d");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/quartic.ml";;
candle_s1_emit_fingerprint "QUARTIC_CASES" QUARTIC_CASES;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\tc8a606f4444ccf303d65289b0e6a3724f8b96b6c92188cc585d9c2bf22b78a3d");;
exit 0;;
