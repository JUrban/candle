print_endline ("CANDLE_REFERENCE_SESSION_V1\t99f842c2a857df61ff92a1c99d772263ad9162a4f29d61a05b00f0e829ca18a6");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/morley.ml";;
candle_s1_emit_fingerprint "MORLEY" MORLEY;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t99f842c2a857df61ff92a1c99d772263ad9162a4f29d61a05b00f0e829ca18a6");;
exit 0;;
