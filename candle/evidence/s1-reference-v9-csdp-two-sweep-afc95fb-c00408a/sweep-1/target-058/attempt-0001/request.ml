print_endline ("CANDLE_REFERENCE_SESSION_V1\tf1c5883f2502e4dd0bbcffa4f96360892055ece2363362ff5a6bd552a9d848c8");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/reciprocity.ml";;
candle_s1_emit_fingerprint "RECIPROCITY_LEGENDRE" RECIPROCITY_LEGENDRE;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\tf1c5883f2502e4dd0bbcffa4f96360892055ece2363362ff5a6bd552a9d848c8");;
exit 0;;
