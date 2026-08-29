module Source_action_internal_semis_module = struct
  let value = List.length [1;2;3];;

  module Nested = struct
    let value = 4;;
  end;;

  let total = begin value + Nested.value end;;
end
