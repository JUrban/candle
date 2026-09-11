type candle_nonlinear_autogen_term = Candle_nonlinear_autogen_term of int;;

module Candle_nonlinear_autogen_value = struct
  let autogen = ref [];;
  let autogen_add term = autogen := !autogen @ [term];;
end;;
