let (THENL_FIRST),(THENL_LAST) =
  let propagate_empty i [] = []
  and propagate_thm th i [] = INSTANTIATE_ALL i th in
  let compose_justs n just1 just2 i ths =
    let ths1,ths2 = chop_list n ths in
    (just1 i ths1)::(just2 i ths2) in
  let rec seqapply l1 l2 = match (l1,l2) with
     ([],[]) -> null_meta,[],propagate_empty
   | ((tac:tactic)::tacs),((goal:goal)::goals) ->
            let ((mvs1,insts1),gls1,just1) = tac goal in
            let goals' = map (inst_goal insts1) goals in
            let ((mvs2,insts2),gls2,just2) = seqapply tacs goals' in
            ((union mvs1 mvs2,compose_insts insts1 insts2),
             gls1@gls2,compose_justs (length gls1) just1 just2)
   | _,_ -> failwith "seqapply: Length mismatch" in
  let justsequence just1 just2 insts2 i ths =
    just1 (compose_insts insts2 i) (just2 i ths) in
  let tacsequence ((mvs1,insts1),gls1,just1) tacl =
    let ((mvs2,insts2),gls2,just2) = seqapply tacl gls1 in
    let jst = justsequence just1 just2 insts2 in
    let just = if gls2 = [] then propagate_thm (jst null_inst []) else jst in
    ((union mvs1 mvs2,compose_insts insts1 insts2),gls2,just) in
  let (thenl_first: tactic -> tactic -> tactic) =
    fun tac1 tac2 g ->
      let _,gls,_ as gstate = tac1 g in
        if gls = [] then failwith "No subgoals"
        else
          let tac_list = tac2 :: (replicate ALL_TAC (length gls - 1)) in
            tacsequence gstate tac_list
  and (thenl_last: tactic -> tactic -> tactic) =
    fun tac1 tac2 g ->
      let _,gls,_ as gstate = tac1 g in
        if gls = [] then failwith "No subgoals"
        else
          let tac_list = (replicate ALL_TAC (length gls - 1)) @ [tac2] in
            tacsequence gstate tac_list in
    thenl_first, thenl_last;;
