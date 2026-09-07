print_endline ("CANDLE_REFERENCE_SESSION_V1\tc331fdae1d2eb3217f9d1ee10217b2f8a92bfdbc763f651c900da62ff25e11ed");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/konigsberg.ml";;
candle_s1_emit_fingerprint "KOENIGSBERG" KOENIGSBERG;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\tc331fdae1d2eb3217f9d1ee10217b2f8a92bfdbc763f651c900da62ff25e11ed");;
exit 0;;
