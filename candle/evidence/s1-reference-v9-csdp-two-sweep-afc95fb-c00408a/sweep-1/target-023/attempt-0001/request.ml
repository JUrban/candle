print_endline ("CANDLE_REFERENCE_SESSION_V1\t4ca35164d3e3fb98e1b17b24ce5dbef4a7a77df1887fb262d199a097a3dbb744");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/divharmonic.ml";;
candle_s1_emit_fingerprint "HARMONIC_DIVERGES" HARMONIC_DIVERGES;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t4ca35164d3e3fb98e1b17b24ce5dbef4a7a77df1887fb262d199a097a3dbb744");;
exit 0;;
