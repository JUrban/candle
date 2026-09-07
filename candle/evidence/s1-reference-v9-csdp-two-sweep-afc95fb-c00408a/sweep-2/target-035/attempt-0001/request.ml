print_endline ("CANDLE_REFERENCE_SESSION_V1\td8848f06a7447417b6289c286434586f4eb9e85e7f920724f1ce85ead61d3e73");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/inclusion_exclusion.ml";;
candle_s1_emit_fingerprint "INCLUSION_EXCLUSION_USUAL" INCLUSION_EXCLUSION_USUAL;;
candle_s1_emit_fingerprint "INCLUSION_EXCLUSION_MOBIUS" INCLUSION_EXCLUSION_MOBIUS;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\td8848f06a7447417b6289c286434586f4eb9e85e7f920724f1ce85ead61d3e73");;
exit 0;;
