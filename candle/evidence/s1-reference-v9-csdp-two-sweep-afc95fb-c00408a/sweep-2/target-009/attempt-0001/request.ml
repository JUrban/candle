print_endline ("CANDLE_REFERENCE_SESSION_V1\t40832e49664c776594012d7a78f10f828c0a5b3da388a971dab039b854d93e6a");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/cayley_hamilton.ml";;
candle_s1_emit_fingerprint "CAYLEY_HAMILTON" CAYLEY_HAMILTON;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t40832e49664c776594012d7a78f10f828c0a5b3da388a971dab039b854d93e6a");;
exit 0;;
