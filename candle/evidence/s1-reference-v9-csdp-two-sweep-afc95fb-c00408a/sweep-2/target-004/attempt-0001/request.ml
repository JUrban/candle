print_endline ("CANDLE_REFERENCE_SESSION_V1\t4e04fa658d42a4c35a34c9f994cef17a9b0145d58fb5b4628e9ec1af299d0989");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/bernoulli.ml";;
candle_s1_emit_fingerprint "SUM_OF_POWERS" SUM_OF_POWERS;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t4e04fa658d42a4c35a34c9f994cef17a9b0145d58fb5b4628e9ec1af299d0989");;
exit 0;;
