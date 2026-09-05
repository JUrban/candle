print_endline ("CANDLE_REFERENCE_SESSION_V1\tc1d188c62149a443a55108433d6d5981213c7c6a6ff82e557dc1dc2ec9c8ee4c");;
loadt "/project/worktrees/candle-reference-v9-launch-652a18a/candle/fingerprint.ml";;
loadt "100/buffon.ml";;
candle_s1_emit_fingerprint "BUFFON_GENERAL" BUFFON_GENERAL;;
candle_s1_emit_fingerprint "BUFFON_SHORT" BUFFON_SHORT;;
candle_s1_emit_fingerprint "BUFFON_LONG" BUFFON_LONG;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\tc1d188c62149a443a55108433d6d5981213c7c6a6ff82e557dc1dc2ec9c8ee4c");;
exit 0;;
