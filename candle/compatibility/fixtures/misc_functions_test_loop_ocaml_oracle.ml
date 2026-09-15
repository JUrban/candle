type event = Clock | Call of int;;

let original clock n f arg =
  let start = clock () in
  let result = f arg in
    for i = 1 to n - 1 do
      let _ = f arg in ()
    done;
    result, clock () - start;;

let normalized clock n f arg =
  let start = clock () in
  let result = f arg in
  let last = n - 1 in
  let rec repeat i =
    if i > last then ()
    else
      let _ = f arg in
        if i = last then () else repeat (i + 1) in
  let _ = repeat 1 in
    result, clock () - start;;

let observe runner n fail_at =
  let events = ref [] and calls = ref 0 and ticks = ref 0 in
  let clock () =
    events := Clock :: !events;
    let tick = !ticks in
    ticks := tick + 7;
    tick in
  let f arg =
    calls := !calls + 1;
    events := Call !calls :: !events;
    if !calls = fail_at then failwith (string_of_int !calls)
    else arg + !calls in
  let outcome =
    try `Result (runner clock n f 40)
    with Failure message -> `Failure message in
  outcome,List.rev !events;;

let assert_same n fail_at =
  let expected = observe original n fail_at
  and actual = observe normalized n fail_at in
  if expected <> actual then failwith "misc_functions test-loop mismatch";;

List.iter
  (fun n ->
     List.iter (assert_same n) [0;1;2;3;4;5;6])
  [-3;0;1;2;5];;

print_endline "MISC_FUNCTIONS_TEST_LOOP_OCAML_ORACLE_OK";;
