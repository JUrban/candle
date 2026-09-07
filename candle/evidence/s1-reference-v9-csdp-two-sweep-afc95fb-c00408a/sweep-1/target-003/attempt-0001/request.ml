print_endline ("CANDLE_REFERENCE_SESSION_V1\tceb82cf01782a1b7cf06f07e58025a888d9ea0de22cd14cb734d3ead690fb670");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/ballot.ml";;
candle_s1_emit_fingerprint "BALLOT" BALLOT;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\tceb82cf01782a1b7cf06f07e58025a888d9ea0de22cd14cb734d3ead690fb670");;
exit 0;;
