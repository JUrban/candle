print_endline ("CANDLE_REFERENCE_SESSION_V1\tf111975b4971af1706fffd090abb4fd6db22932425bb3f890c3c86687a440d6f");;
loadt "/project/worktrees/candle-reference-v9-launch-652a18a/candle/fingerprint.ml";;
loadt "100/bertrand.ml";;
loadt "100/primerecip.ml";;
candle_s1_emit_fingerprint "BERTRAND" BERTRAND;;
candle_s1_emit_fingerprint "PRIMERECIP_DIVERGES" PRIMERECIP_DIVERGES;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\tf111975b4971af1706fffd090abb4fd6db22932425bb3f890c3c86687a440d6f");;
exit 0;;
