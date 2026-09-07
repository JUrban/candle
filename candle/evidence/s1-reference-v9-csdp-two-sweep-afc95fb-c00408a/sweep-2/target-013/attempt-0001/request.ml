print_endline ("CANDLE_REFERENCE_SESSION_V1\t07e3439dae32a6d07a4e8cc9017cb9e2eff383b688c423c562943eb1d32ec16d");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/combinations.ml";;
candle_s1_emit_fingerprint "NUMBER_OF_COMBINATIONS" NUMBER_OF_COMBINATIONS;;
candle_s1_emit_fingerprint "NUMBER_OF_COMBINATIONS_EXPLICIT" NUMBER_OF_COMBINATIONS_EXPLICIT;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t07e3439dae32a6d07a4e8cc9017cb9e2eff383b688c423c562943eb1d32ec16d");;
exit 0;;
