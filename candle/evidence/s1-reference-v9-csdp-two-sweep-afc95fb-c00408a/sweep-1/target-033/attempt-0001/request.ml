print_endline ("CANDLE_REFERENCE_SESSION_V1\t8c911bb461fe307044bb2d0a83a9aaf882ab05545b302066c5f9b128e3d343d5");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/heron.ml";;
candle_s1_emit_fingerprint "HERON" HERON;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t8c911bb461fe307044bb2d0a83a9aaf882ab05545b302066c5f9b128e3d343d5");;
exit 0;;
