print_endline ("CANDLE_REFERENCE_SESSION_V1\te7ca39bed2aae35f04fd7ece2b629721ae5d7bfdc94f500f7540eba25f5e8be8");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/cayley_hamilton.ml";;
candle_s1_emit_fingerprint "CAYLEY_HAMILTON" CAYLEY_HAMILTON;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\te7ca39bed2aae35f04fd7ece2b629721ae5d7bfdc94f500f7540eba25f5e8be8");;
exit 0;;
