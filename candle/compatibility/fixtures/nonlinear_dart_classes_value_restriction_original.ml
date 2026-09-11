type candle_nonlinear_dart_thm = Candle_nonlinear_dart_thm of int;;

module Candle_nonlinear_dart_classes_value = struct
  let dart_classes = ref [];;
  let define_dart th =
    let _ = dart_classes := th::!dart_classes in
    th;;
end;;
