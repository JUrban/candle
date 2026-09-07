print_endline ("CANDLE_REFERENCE_SESSION_V1\tcfd4dbcf4457e4e3a4ea4d9449b81bd116bb402499de05c4305381643a82f556");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/circle.ml";;
candle_s1_emit_fingerprint "AREA_CBALL" AREA_CBALL;;
candle_s1_emit_fingerprint "AREA_BALL" AREA_BALL;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\tcfd4dbcf4457e4e3a4ea4d9449b81bd116bb402499de05c4305381643a82f556");;
exit 0;;
