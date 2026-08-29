(* In-process source preflight for the manifest-rooted Flyspeck loader. *)

let candle_flyspeck_verify_source candle_root flyspeck_root
                                     (repository,path,expected) =
  let root =
    if repository = "candle" then candle_root
    else if repository = "flyspeck" then flyspeck_root
    else failwith ("unknown Flyspeck source repository: " ^ repository) in
  let source = Filename.concat root path in
  if not (Sys.file_exists source) then
    failwith ("missing pinned source before Flyspeck build: " ^
              repository ^ ":" ^ path)
  else
    let actual = Digest.to_hex (Digest.file source) in
    if actual <> expected then
      failwith ("source digest mismatch before Flyspeck build: " ^
                repository ^ ":" ^ path);;

let candle_flyspeck_verify_sources expected_count candle_root flyspeck_root
                                      sources =
  if List.length sources <> expected_count then
    failwith "incomplete Flyspeck source digest program"
  else
    List.iter
      (candle_flyspeck_verify_source candle_root flyspeck_root)
      sources;;
