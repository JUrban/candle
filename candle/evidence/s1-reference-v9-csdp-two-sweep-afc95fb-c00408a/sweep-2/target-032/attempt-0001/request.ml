print_endline ("CANDLE_REFERENCE_SESSION_V1\td7577b66b71786fd5668a2b2be08010fdf33cc685369b5c7f1b7feade5c306d1");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/green.ml";;
candle_s1_emit_fingerprint "GREEN_THEOREM_CURL" GREEN_THEOREM_CURL;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\td7577b66b71786fd5668a2b2be08010fdf33cc685369b5c7f1b7feade5c306d1");;
exit 0;;
