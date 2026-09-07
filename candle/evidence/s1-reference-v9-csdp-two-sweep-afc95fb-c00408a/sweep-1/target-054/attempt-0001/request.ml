print_endline ("CANDLE_REFERENCE_SESSION_V1\ta4c95b68ec93459549933662c8cea5fa5e0843a4c607206fbd44b1bd8e42d248");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/quartic.ml";;
candle_s1_emit_fingerprint "QUARTIC_CASES" QUARTIC_CASES;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\ta4c95b68ec93459549933662c8cea5fa5e0843a4c607206fbd44b1bd8e42d248");;
exit 0;;
