print_endline ("CANDLE_REFERENCE_SESSION_V1\t4fc6a74fec3262fba5e362bf4018bce0df1988f333eca83894a1157e0957d5ce");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/arithmetic.ml";;
candle_s1_emit_fingerprint "ARITHMETIC_PROGRESSION" ARITHMETIC_PROGRESSION;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t4fc6a74fec3262fba5e362bf4018bce0df1988f333eca83894a1157e0957d5ce");;
exit 0;;
