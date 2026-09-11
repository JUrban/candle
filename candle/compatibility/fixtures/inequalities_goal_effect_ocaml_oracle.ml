let original_trace = ref [];;
let original_g term = original_trace := term::!original_trace; [term];;

module Original = struct
  let goal_concl = true;;
  original_g(goal_concl);;
  let goal_theorem = goal_concl;;
end;;

let normalized_trace = ref [];;
let normalized_g term = normalized_trace := term::!normalized_trace; [term];;

module Normalized = struct
  let goal_concl = true;;
  let _ = normalized_g(goal_concl);;
  let goal_theorem = goal_concl;;
end;;

let () =
  if !original_trace = !normalized_trace &&
     !normalized_trace = [true] &&
     Original.goal_theorem = Normalized.goal_theorem then
    print_endline "INEQUALITIES_GOAL_EFFECT_OCAML_ORACLE_OK"
  else failwith "Inequalities goal-effect oracle mismatch";;
