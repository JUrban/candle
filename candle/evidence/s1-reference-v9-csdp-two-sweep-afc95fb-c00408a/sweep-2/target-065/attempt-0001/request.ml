print_endline ("CANDLE_REFERENCE_SESSION_V1\t436a2c9c53cc58144f5605e748a41a96a7cf2b9b0a62f6870392498258b3977c");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/wilson.ml";;
candle_s1_emit_fingerprint "WILSON" WILSON;;
candle_s1_emit_fingerprint "WILSON_EQ" WILSON_EQ;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t436a2c9c53cc58144f5605e748a41a96a7cf2b9b0a62f6870392498258b3977c");;
exit 0;;
