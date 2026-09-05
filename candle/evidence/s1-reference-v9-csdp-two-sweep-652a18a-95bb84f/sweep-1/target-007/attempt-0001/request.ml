print_endline ("CANDLE_REFERENCE_SESSION_V1\t0cb5179674c8e383c96f85ceee9119971fe54da6bb2da2f2693b2ab6e555c230");;
loadt "/project/worktrees/candle-reference-v9-launch-652a18a/candle/fingerprint.ml";;
loadt "100/buffon.ml";;
candle_s1_emit_fingerprint "BUFFON_GENERAL" BUFFON_GENERAL;;
candle_s1_emit_fingerprint "BUFFON_SHORT" BUFFON_SHORT;;
candle_s1_emit_fingerprint "BUFFON_LONG" BUFFON_LONG;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t0cb5179674c8e383c96f85ceee9119971fe54da6bb2da2f2693b2ab6e555c230");;
exit 0;;
