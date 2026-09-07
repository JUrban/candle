print_endline ("CANDLE_REFERENCE_SESSION_V1\t80b65f6d0b0d1f79d68d22ba5569c66d14f9a4fc1c206f35a8595cbe1205eb09");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/cosine.ml";;
candle_s1_emit_fingerprint "LAW_OF_COSINES" LAW_OF_COSINES;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t80b65f6d0b0d1f79d68d22ba5569c66d14f9a4fc1c206f35a8595cbe1205eb09");;
exit 0;;
