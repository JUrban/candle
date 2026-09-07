print_endline ("CANDLE_REFERENCE_SESSION_V1\t18cdd5fd40b0856c9a2155eeb535e6c7b6e220337f3a8531c86fd481e9f88d78");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/inclusion_exclusion.ml";;
candle_s1_emit_fingerprint "INCLUSION_EXCLUSION_USUAL" INCLUSION_EXCLUSION_USUAL;;
candle_s1_emit_fingerprint "INCLUSION_EXCLUSION_MOBIUS" INCLUSION_EXCLUSION_MOBIUS;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t18cdd5fd40b0856c9a2155eeb535e6c7b6e220337f3a8531c86fd481e9f88d78");;
exit 0;;
