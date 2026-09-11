let rec candle_nonlinear_nth values index =
  match values,index with
  | head::_,0 -> head
  | _::tail,n -> candle_nonlinear_nth tail (n - 1)
  | [],_ -> failwith "nth";;

let candle_nonlinear_mixed_nth pairs tuples =
  (candle_nonlinear_nth pairs 0,candle_nonlinear_nth tuples 0);;

let candle_nonlinear_nth_normalized =
  candle_nonlinear_mixed_nth
    ["term"]
    [("a","b","c","d")];;

let candle_nonlinear_nth_alias_ok =
  candle_nonlinear_nth_normalized =
    ("term",("a","b","c","d"));;
