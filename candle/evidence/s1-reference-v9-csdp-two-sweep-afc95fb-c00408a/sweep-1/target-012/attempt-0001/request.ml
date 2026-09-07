print_endline ("CANDLE_REFERENCE_SESSION_V1\tcc5b5fa4becb40234af3f1a56da472d5795f40e1b6868258f6172b7daab736cc");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/chords.ml";;
candle_s1_emit_fingerprint "SEGMENT_CHORDS" SEGMENT_CHORDS;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\tcc5b5fa4becb40234af3f1a56da472d5795f40e1b6868258f6172b7daab736cc");;
exit 0;;
