print_endline ("CANDLE_REFERENCE_SESSION_V1\ta8ae81e2872470c30e5e685dab722de8026af02cd8870987a8665836c5d26a60");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/ceva.ml";;
candle_s1_emit_fingerprint "CEVA" CEVA;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\ta8ae81e2872470c30e5e685dab722de8026af02cd8870987a8665836c5d26a60");;
exit 0;;
