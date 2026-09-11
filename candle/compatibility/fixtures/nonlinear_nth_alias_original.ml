let rec candle_nonlinear_nth values index =
  match values,index with
  | head::_,0 -> head
  | _::tail,n -> candle_nonlinear_nth tail (n - 1)
  | [],_ -> failwith "nth";;

let candle_nonlinear_mixed_nth pairs tuples =
  let nth = candle_nonlinear_nth in
  (nth pairs 0,nth tuples 0);;

let candle_nonlinear_nth_original =
  candle_nonlinear_mixed_nth
    ["term"]
    [("a","b","c","d")];;
