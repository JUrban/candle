print_endline ("CANDLE_REFERENCE_SESSION_V1\t68c19a7d40b325a1625422c177f0cacafe5d5fae0d0888b610897aa3d7da78b9");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/combinations.ml";;
candle_s1_emit_fingerprint "NUMBER_OF_COMBINATIONS" NUMBER_OF_COMBINATIONS;;
candle_s1_emit_fingerprint "NUMBER_OF_COMBINATIONS_EXPLICIT" NUMBER_OF_COMBINATIONS_EXPLICIT;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t68c19a7d40b325a1625422c177f0cacafe5d5fae0d0888b610897aa3d7da78b9");;
exit 0;;
