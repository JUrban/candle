print_endline ("CANDLE_REFERENCE_SESSION_V1\t91761011982c43c1f06875aafc4ecc999dba11f63ea57da8308cdf482000ba39");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/heron.ml";;
candle_s1_emit_fingerprint "HERON" HERON;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t91761011982c43c1f06875aafc4ecc999dba11f63ea57da8308cdf482000ba39");;
exit 0;;
