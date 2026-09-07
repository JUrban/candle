print_endline ("CANDLE_REFERENCE_SESSION_V1\tb05b642ceb5e06438fb54b2a2ab7c1c59e905b847ade77c5b1d9d4afc1458aee");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/friendship.ml";;
candle_s1_emit_fingerprint "FRIENDSHIP" FRIENDSHIP;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\tb05b642ceb5e06438fb54b2a2ab7c1c59e905b847ade77c5b1d9d4afc1458aee");;
exit 0;;
