module Candle_inequalities_goal_original = struct
  let goal_concl = `T`;;
  g(goal_concl);;
  let goal_theorem = prove(goal_concl,REWRITE_TAC[]);;
end;;
