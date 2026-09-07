print_endline ("CANDLE_REFERENCE_SESSION_V1\t224d39066184cd209f6dd10885c5954611b791287746a41db6075afb7ae10e1a");;
loadt "/project/worktrees/candle-v3-reference-collector-v13/candle/fingerprint_v3.ml";;
loadt "100/cubedissection.ml";;
candle_s1_emit_fingerprint "ONLY_TRIVIAL_CUBE_DISSECTION" ONLY_TRIVIAL_CUBE_DISSECTION;;
candle_s1_emit_state_fingerprint ();;
print_endline ("CANDLE_REFERENCE_COMPLETE_V1\t224d39066184cd209f6dd10885c5954611b791287746a41db6075afb7ae10e1a");;
exit 0;;
