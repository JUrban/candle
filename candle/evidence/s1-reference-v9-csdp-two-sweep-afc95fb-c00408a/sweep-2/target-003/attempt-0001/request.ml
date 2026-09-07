print_endline ("CANDLE_REFERENCE_SESSION_V1\t4faaa48b75cd87c7f3b8d50a46cef50046982ce522de73047b7808a77ed857dc");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/ballot.ml";;
candle_s1_emit_fingerprint "BALLOT" BALLOT;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t4faaa48b75cd87c7f3b8d50a46cef50046982ce522de73047b7808a77ed857dc");;
exit 0;;
