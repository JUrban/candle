print_endline ("CANDLE_REFERENCE_SESSION_V1\t0ab2a506fccfe0804dd45b8969ed43f6e7856eecc7750d187cd0682220d96d66");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/gcd.ml";;
candle_s1_emit_fingerprint "EGCD" EGCD;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t0ab2a506fccfe0804dd45b8969ed43f6e7856eecc7750d187cd0682220d96d66");;
exit 0;;
