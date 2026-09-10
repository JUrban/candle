let candle_flyspeck_original_all_forall bod =
  let mk_forall = mk_binder "!" in
  itlist (curry mk_forall) (sort (<) (frees bod)) bod;;
