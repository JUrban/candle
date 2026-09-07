print_endline ("CANDLE_REFERENCE_SESSION_V1\te176143ef6a68d117313ef60d19d67a8c78c73ecd69ae2cdc6d8f30da2ce6a5c");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/reciprocity.ml";;
candle_s1_emit_fingerprint "RECIPROCITY_LEGENDRE" RECIPROCITY_LEGENDRE;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\te176143ef6a68d117313ef60d19d67a8c78c73ecd69ae2cdc6d8f30da2ce6a5c");;
exit 0;;
