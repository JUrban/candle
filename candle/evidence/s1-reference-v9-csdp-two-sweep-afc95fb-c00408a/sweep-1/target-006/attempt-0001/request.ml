print_endline ("CANDLE_REFERENCE_SESSION_V1\t803152755f98bf3a2c02e2511b493cf5e1471a4f8c747e01d3fe765a96286f4e");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/birthday.ml";;
candle_s1_emit_fingerprint "BIRTHDAY_THM" BIRTHDAY_THM;;
candle_s1_emit_fingerprint "BIRTHDAY_THM_EXPLICIT" BIRTHDAY_THM_EXPLICIT;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t803152755f98bf3a2c02e2511b493cf5e1471a4f8c747e01d3fe765a96286f4e");;
exit 0;;
