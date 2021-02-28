let add_expr_vars expr_vars vars var =
  let is_exists_in_vars = List.exists (fun v -> String.equal v var) vars
  in let is_dup = List.exists (fun v -> String.equal v var) expr_vars
  in if is_exists_in_vars & not is_dup 
     then var :: expr_vars
     else expr_vars

let rec get_variables_in_expr expr expr_vars vars =
  match expr with
  | (Sexp.Atom v) :: tl -> 
                      get_variables_in_expr tl (add_expr_vars expr_vars vars v) vars
  | (Sexp.Expr hd) :: tl ->
                      let head_vars = get_variables_in_expr hd expr_vars vars
                        in get_variables_in_expr tl head_vars vars
  | [] -> expr_vars