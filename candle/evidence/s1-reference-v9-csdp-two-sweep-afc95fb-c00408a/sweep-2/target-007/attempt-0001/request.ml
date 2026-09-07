print_endline ("CANDLE_REFERENCE_SESSION_V1\t37422d197d223abd4454eeb04e7afc860eae7747239d6e062ca8cac616510dff");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/buffon.ml";;
candle_s1_emit_fingerprint "BUFFON_GENERAL" BUFFON_GENERAL;;
candle_s1_emit_fingerprint "BUFFON_SHORT" BUFFON_SHORT;;
candle_s1_emit_fingerprint "BUFFON_LONG" BUFFON_LONG;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t37422d197d223abd4454eeb04e7afc860eae7747239d6e062ca8cac616510dff");;
exit 0;;
