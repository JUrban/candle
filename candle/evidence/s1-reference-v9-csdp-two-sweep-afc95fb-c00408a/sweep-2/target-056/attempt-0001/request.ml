print_endline ("CANDLE_REFERENCE_SESSION_V1\t6be6e2a44432f6beba976bba7c3c95e72ffd5482ba2ed2707e46594b39f3b69d");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/ratcountable.ml";;
candle_s1_emit_fingerprint "COUNTABLE_RATIONALS" COUNTABLE_RATIONALS;;
candle_s1_emit_fingerprint "DENUMERABLE_RATIONALS" DENUMERABLE_RATIONALS;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t6be6e2a44432f6beba976bba7c3c95e72ffd5482ba2ed2707e46594b39f3b69d");;
exit 0;;
