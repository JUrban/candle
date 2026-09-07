print_endline ("CANDLE_REFERENCE_SESSION_V1\tcfa7e5ca52ccb951ac35f9d2d67938804e64a3b665bcd6eb90210f0c67e50f58");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/bertrand.ml";;
loadt "100/primerecip.ml";;
candle_s1_emit_fingerprint "BERTRAND" BERTRAND;;
candle_s1_emit_fingerprint "PRIMERECIP_DIVERGES" PRIMERECIP_DIVERGES;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\tcfa7e5ca52ccb951ac35f9d2d67938804e64a3b665bcd6eb90210f0c67e50f58");;
exit 0;;
