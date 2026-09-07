print_endline ("CANDLE_REFERENCE_SESSION_V1\t8c65784635441712a53d909d590abf2401deddcaf041700c67029d9e79d75637");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/arithmetic_geometric_mean.ml";;
candle_s1_emit_fingerprint "AGM" AGM;;
candle_s1_emit_fingerprint "AGM_ROOT" AGM_ROOT;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t8c65784635441712a53d909d590abf2401deddcaf041700c67029d9e79d75637");;
exit 0;;
