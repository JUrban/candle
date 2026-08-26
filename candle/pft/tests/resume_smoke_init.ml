#use "hol.ml";;

let resume_smoke_script =
  try Sys.getenv "CANDLE_PFT_RESUME_SCRIPT"
  with Not_found -> failwith "CANDLE_PFT_RESUME_SCRIPT is not set";;

loadt resume_smoke_script;;
