print_endline ("CANDLE_REFERENCE_SESSION_V1\te1171de76b34920dc1394669301aa8eb43e2d9b5d42aeae4f99a8454f6395c90");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/ratcountable.ml";;
candle_s1_emit_fingerprint "COUNTABLE_RATIONALS" COUNTABLE_RATIONALS;;
candle_s1_emit_fingerprint "DENUMERABLE_RATIONALS" DENUMERABLE_RATIONALS;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\te1171de76b34920dc1394669301aa8eb43e2d9b5d42aeae4f99a8454f6395c90");;
exit 0;;
