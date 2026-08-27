let candle_semicolon_identity x = x;;

module Pm_eqn4_rhs = struct
  let marker = candle_semicolon_identity
    (candle_semicolon_identity 1;)
end;;
