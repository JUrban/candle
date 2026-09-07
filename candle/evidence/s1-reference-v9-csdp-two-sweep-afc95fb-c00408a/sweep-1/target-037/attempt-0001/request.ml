print_endline ("CANDLE_REFERENCE_SESSION_V1\tbbe7b8627ee1312dc6e96630f0b672d5332a330231ed9766b0bfdda98e2ee098");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/isosceles.ml";;
candle_s1_emit_fingerprint "ISOSCELES_TRIANGLE_THEOREM" ISOSCELES_TRIANGLE_THEOREM;;
candle_s1_emit_fingerprint "ISOSCELES_TRIANGLE_CONVERSE" ISOSCELES_TRIANGLE_CONVERSE;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\tbbe7b8627ee1312dc6e96630f0b672d5332a330231ed9766b0bfdda98e2ee098");;
exit 0;;
