let (|->) x y t =
  let newbranch p1 t1 p2 t2 =
    let zp = p1 lxor p2 in
    let b = zp land (-zp) in
    let p = p1 land (b - 1) in
    if p1 land b = 0 then Branch(p,b,t1,t2)
    else Branch(p,b,t2,t1) in
  let rec define_list (x,y as xy) l =
    match l with
      (a,b as ab)::t ->
          let c = Stdlib.compare x a in
          if c = 0 then xy::t
          else if c < 0 then xy::l
          else ab::(define_list xy t)
    | [] -> [xy] in
  let k = Hashtbl.hash x in
  let rec upd t =
    match t with
      Empty -> Leaf (k,[x,y])
    | Leaf(h,l) ->
         if h = k then Leaf(h,define_list (x,y) l)
         else newbranch h t k (Leaf(k,[x,y]))
    | Branch(p,b,l,r) ->
        if k land (b - 1) <> p then newbranch p t k (Leaf(k,[x,y]))
        else if k land b = 0 then Branch(p,b,upd l,r)
        else Branch(p,b,l,upd r) in
  upd t;;

let combine op z t1 t2 =
  let newbranch p1 t1 p2 t2 =
    let zp = p1 lxor p2 in
    let b = zp land (-zp) in
    let p = p1 land (b - 1) in
    if p1 land b = 0 then Branch(p,b,t1,t2)
    else Branch(p,b,t2,t1) in
  let rec combine_list op z l1 l2 =
    match (l1,l2) with
      [],_ -> l2
    | _,[] -> l1
    | ((x1,y1 as xy1)::t1,(x2,y2 as xy2)::t2) ->
          let c = Stdlib.compare x1 x2 in
          if c < 0 then xy1::(combine_list op z t1 l2)
          else if c > 0 then xy2::(combine_list op z l1 t2) else
          let y = op y1 y2 and l = combine_list op z t1 t2 in
          if z(y) then l else (x1,y)::l in
  let rec combine op z t1 t2 =
    match (t1,t2) with
      Empty,_ -> t2
    | _,Empty -> t1
    | Leaf(h1,l1),Leaf(h2,l2) ->
          if h1 = h2 then
            let l = combine_list op z l1 l2 in
            if l = [] then Empty else Leaf(h1,l)
          else newbranch h1 t1 h2 t2
    | (Leaf(k,lis) as lf),(Branch(p,b,l,r) as br) ->
          if k land (b - 1) = p then
            if k land b = 0 then
              (match combine op z lf l with
                 Empty -> r | l' -> Branch(p,b,l',r))
            else
              (match combine op z lf r with
                 Empty -> l | r' -> Branch(p,b,l,r'))
          else
            newbranch k lf p br
    | (Branch(p,b,l,r) as br),(Leaf(k,lis) as lf) ->
          if k land (b - 1) = p then
            if k land b = 0 then
              (match combine op z l lf with
                Empty -> r | l' -> Branch(p,b,l',r))
            else
              (match combine op z r lf with
                 Empty -> l | r' -> Branch(p,b,l,r'))
          else
            newbranch p br k lf
    | Branch(p1,b1,l1,r1),Branch(p2,b2,l2,r2) ->
          if b1 < b2 then
            if p2 land (b1 - 1) <> p1 then newbranch p1 t1 p2 t2
            else if p2 land b1 = 0 then
              (match combine op z l1 t2 with
                 Empty -> r1 | l -> Branch(p1,b1,l,r1))
            else
              (match combine op z r1 t2 with
                 Empty -> l1 | r -> Branch(p1,b1,l1,r))
          else if b2 < b1 then
            if p1 land (b2 - 1) <> p2 then newbranch p1 t1 p2 t2
            else if p1 land b2 = 0 then
              (match combine op z t1 l2 with
                 Empty -> r2 | l -> Branch(p2,b2,l,r2))
            else
              (match combine op z t1 r2 with
                 Empty -> l2 | r -> Branch(p2,b2,l2,r))
          else if p1 = p2 then
           (match (combine op z l1 l2,combine op z r1 r2) with
              (Empty,r) -> r | (l,Empty) -> l | (l,r) -> Branch(p1,b1,l,r))
          else
            newbranch p1 t1 p2 t2 in
  combine op z t1 t2;;
