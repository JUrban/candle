let candle_expect_list_comparator
    (cmp : int list -> int list -> bool) = cmp;;

let candle_unqualified_list_comparator =
  candle_expect_list_comparator (<);;
