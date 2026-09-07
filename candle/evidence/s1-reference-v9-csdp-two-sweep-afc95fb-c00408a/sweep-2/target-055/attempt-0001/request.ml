print_endline ("CANDLE_REFERENCE_SESSION_V1\t2d51d79e5aa81ea93941cbe44a08414c16c42c83cbb3bb5d6ae1b2d748be97d7");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/ramsey.ml";;
candle_s1_emit_fingerprint "RAMSEY" RAMSEY;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t2d51d79e5aa81ea93941cbe44a08414c16c42c83cbb3bb5d6ae1b2d748be97d7");;
exit 0;;
