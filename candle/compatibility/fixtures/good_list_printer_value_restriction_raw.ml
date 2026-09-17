let candle_good_list_trace : int list ref = ref [];;

let candle_good_list_record x =
  candle_good_list_trace := x :: !candle_good_list_trace;;

let candle_good_list_printer =
  let rec print_sequence sep = function
    | [] -> ()
    | h :: ts ->
        let _ = candle_good_list_record h in
        if ts = [] then ()
        else let _ = candle_good_list_record sep in
             print_sequence sep ts in
  fun form xs ->
    let _ = form in
    print_sequence 0 xs;;

let _ = candle_good_list_printer "string-form" [1; 2; 3];;
let _ = candle_good_list_printer 17 [4; 5];;
let candle_good_list_observation = !candle_good_list_trace;;
