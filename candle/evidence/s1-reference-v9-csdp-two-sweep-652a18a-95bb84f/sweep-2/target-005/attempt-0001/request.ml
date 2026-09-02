print_endline ("CANDLE_REFERENCE_SESSION_V1\t5ed03388a811676cf4ab2056a9803cfcbb2846c0a6e5faafa2efdff289f1f181");;
loadt "/project/worktrees/candle-reference-v9-launch-652a18a/candle/fingerprint.ml";;
loadt "100/bertrand.ml";;
loadt "100/primerecip.ml";;
candle_s1_emit_fingerprint "BERTRAND" BERTRAND;;
candle_s1_emit_fingerprint "PRIMERECIP_DIVERGES" PRIMERECIP_DIVERGES;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t5ed03388a811676cf4ab2056a9803cfcbb2846c0a6e5faafa2efdff289f1f181");;
exit 0;;
