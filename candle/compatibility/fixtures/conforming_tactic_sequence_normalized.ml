let candle_conforming_tactic_sequence =
  fun th ->
    MP_TAC th THEN REWRITE_TAC[] THEN ASSUME_TAC th THEN STRIP_TAC;;
