print_endline ("CANDLE_REFERENCE_SESSION_V1\t1ab53bc27feac0e49e729fad5d9d3dfd7b4ae73a3ab9e6aa32feb71170de2446");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/bertrand.ml";;
loadt "100/primerecip.ml";;
candle_s1_emit_fingerprint "BERTRAND" BERTRAND;;
candle_s1_emit_fingerprint "PRIMERECIP_DIVERGES" PRIMERECIP_DIVERGES;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t1ab53bc27feac0e49e729fad5d9d3dfd7b4ae73a3ab9e6aa32feb71170de2446");;
exit 0;;
