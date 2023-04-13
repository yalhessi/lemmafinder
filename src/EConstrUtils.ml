let rec fold (sigma : Evd.evar_map) (f : 'a -> Evd.econstr -> 'a) (acc: 'a) (econstr : EConstr.t)  = 
  let acc' = f acc econstr in 
  let fold' = fold sigma f in
  match EConstr.kind sigma econstr with
  | Cast(ty1,ck,ty2) -> 
    let acc'' = fold' acc' ty1 in
    fold' acc'' ty2
  | Prod(na, ty, c) -> 
    let acc'' = fold' acc' ty in
    fold' acc'' c
  | Lambda(na,ty,c) ->
    let acc'' = fold' acc' ty in
    fold' acc'' c
  | LetIn (na,b,ty,c) -> 
    let acc'' = fold' acc' b in
    let acc''' = fold' acc'' ty in
    fold' acc''' c
  | App(f,args) -> 
    let acc'' = fold' acc' f in
    Array.fold_left fold' acc'' args
  | Case(ci, u, params, p, iv, c, brs) -> 
    let acc'' = fold' acc' c in
    let bl = Array.map (fun (na, b) -> b) brs in
    Array.fold_left fold' acc'' bl
  | Rel(_) | Var(_) | Meta(_) | Evar(_) | Sort(_)  | Ind(_,_) | Construct(_,_) | Fix(_,_) | CoFix(_,_) | Proj(_,_) | Int(_) | Float(_) | Const(_,_) -> acc'