print_endline ("CANDLE_REFERENCE_SESSION_V1\tcb213ec61209b4585dcf1a3fa3b2b7d177f98668555f5bcf84200635911f2c72");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/dirichlet.ml";;
candle_s1_emit_fingerprint "DIRICHLET" DIRICHLET;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\tcb213ec61209b4585dcf1a3fa3b2b7d177f98668555f5bcf84200635911f2c72");;
exit 0;;
