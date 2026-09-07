print_endline ("CANDLE_REFERENCE_SESSION_V1\t787985cfd31360ab97cade6b54437119f38efece3530966abd151fe29f3fc3f2");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/circle.ml";;
candle_s1_emit_fingerprint "AREA_CBALL" AREA_CBALL;;
candle_s1_emit_fingerprint "AREA_BALL" AREA_BALL;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t787985cfd31360ab97cade6b54437119f38efece3530966abd151fe29f3fc3f2");;
exit 0;;
