type candle_optimize_preprocess_datum = {
  candle_optimize_preprocess_id : string;
  candle_optimize_preprocess_tags : int list;
  candle_optimize_preprocess_value : int
};;

let candle_optimize_preprocess_fields datum =
  (datum.candle_optimize_preprocess_id,
   datum.candle_optimize_preprocess_tags,
   datum.candle_optimize_preprocess_value);;

let candle_optimize_preprocess triple = triple;;

let candle_optimize_preprocess_split datum =
  let name,tags,value = candle_optimize_preprocess_fields datum in
  [candle_optimize_preprocess ("prep-" ^ name,tags,value)];;

let candle_optimize_preprocess_result =
  candle_optimize_preprocess_split {
    candle_optimize_preprocess_id = "probe";
    candle_optimize_preprocess_tags = [1;2];
    candle_optimize_preprocess_value = 3
  };;
