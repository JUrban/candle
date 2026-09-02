print_endline ("CANDLE_REFERENCE_SESSION_V1\t95bf5b302249fe23468c1d95cf89290e80b8780994cd96555baf75aeecabb7fe");;
loadt "/project/worktrees/candle-reference-v9-launch-652a18a/candle/fingerprint.ml";;
loadt "100/konigsberg.ml";;
candle_s1_emit_fingerprint "KOENIGSBERG" KOENIGSBERG;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t95bf5b302249fe23468c1d95cf89290e80b8780994cd96555baf75aeecabb7fe");;
exit 0;;
