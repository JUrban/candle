print_endline ("CANDLE_REFERENCE_SESSION_V1\t02468faf84a8a28cbda995cb678c1ff262541dfc086725a2c4e64fc061d9e443");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/constructible.ml";;
candle_s1_emit_fingerprint "DOUBLE_THE_CUBE" DOUBLE_THE_CUBE;;
candle_s1_emit_fingerprint "TRISECT_60_DEGREES" TRISECT_60_DEGREES;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t02468faf84a8a28cbda995cb678c1ff262541dfc086725a2c4e64fc061d9e443");;
exit 0;;
