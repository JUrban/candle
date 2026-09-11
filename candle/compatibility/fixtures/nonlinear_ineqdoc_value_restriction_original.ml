type candle_nonlinear_texmarker =
  | Candle_nonlinear_section
  | Candle_nonlinear_ineqdoc
  | Candle_nonlinear_comment;;

module Candle_nonlinear_ineqdoc_value = struct
  let ineqdoc = ref [];;
  let addtex (marker,name,text) =
    ineqdoc := (marker,name,text)::!ineqdoc;;
end;;
