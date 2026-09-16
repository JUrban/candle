module Candle_inequalities_goal_original = struct
  let goal_concl = `T`;;
  g(goal_concl);;
  let goal_theorem = prove(goal_concl,REWRITE_TAC[]);;
end;;

let candle_inequalities_goal_original_ok =
  concl Candle_inequalities_goal_original.goal_theorem = `T`;;
