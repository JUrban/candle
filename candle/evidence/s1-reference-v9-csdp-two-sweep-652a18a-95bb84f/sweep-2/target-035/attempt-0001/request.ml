print_endline ("CANDLE_REFERENCE_SESSION_V1\tfa056c444a6fc05ed621033d7a02e0019d6b558b68e05a542c72efed1009a6e5");;
loadt "/project/worktrees/candle-reference-v9-launch-652a18a/candle/fingerprint.ml";;
loadt "100/inclusion_exclusion.ml";;
candle_s1_emit_fingerprint "INCLUSION_EXCLUSION_USUAL" INCLUSION_EXCLUSION_USUAL;;
candle_s1_emit_fingerprint "INCLUSION_EXCLUSION_MOBIUS" INCLUSION_EXCLUSION_MOBIUS;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\tfa056c444a6fc05ed621033d7a02e0019d6b558b68e05a542c72efed1009a6e5");;
exit 0;;
