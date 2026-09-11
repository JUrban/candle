module Candle_inequalities_goal_normalized = struct
  let goal_concl = `T`;;
  let _ = g(goal_concl);;
  let goal_theorem = prove(goal_concl,REWRITE_TAC[]);;
end;;

let candle_inequalities_goal_effect_ok =
  concl Candle_inequalities_goal_normalized.goal_theorem = `T`;;
