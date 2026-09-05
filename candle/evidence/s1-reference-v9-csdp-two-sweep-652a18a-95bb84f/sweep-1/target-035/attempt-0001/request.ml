print_endline ("CANDLE_REFERENCE_SESSION_V1\t9f821ea6808a8718cdea7afc9e099035007594b1524e48a3f740df78bd463277");;
loadt "/project/worktrees/candle-reference-v9-launch-652a18a/candle/fingerprint.ml";;
loadt "100/inclusion_exclusion.ml";;
candle_s1_emit_fingerprint "INCLUSION_EXCLUSION_USUAL" INCLUSION_EXCLUSION_USUAL;;
candle_s1_emit_fingerprint "INCLUSION_EXCLUSION_MOBIUS" INCLUSION_EXCLUSION_MOBIUS;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t9f821ea6808a8718cdea7afc9e099035007594b1524e48a3f740df78bd463277");;
exit 0;;
