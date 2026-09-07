print_endline ("CANDLE_REFERENCE_SESSION_V1\t4550fbc3a9beacacea38ca593bf571759a75516e3ee4b824916b1c19bd53ef80");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/konigsberg.ml";;
candle_s1_emit_fingerprint "KOENIGSBERG" KOENIGSBERG;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t4550fbc3a9beacacea38ca593bf571759a75516e3ee4b824916b1c19bd53ef80");;
exit 0;;
