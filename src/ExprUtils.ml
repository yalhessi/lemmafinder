open Sexp

let add_expr_vars expr_vars vars var =
  let is_exists_in_vars = List.exists (fun v -> String.equal v var) vars
  in let is_dup = List.exists (fun v -> String.equal v var) expr_vars
  in if is_exists_in_vars & not is_dup 
     then var :: expr_vars
     else expr_vars

let rec get_variables_in_expr expr expr_vars vars =
  match expr with
  | (Atom v) :: tl -> 
                      get_variables_in_expr tl (add_expr_vars expr_vars vars v) vars
  | (Expr hd) :: tl ->
                      let head_vars = get_variables_in_expr hd expr_vars vars
                        in get_variables_in_expr tl head_vars vars
  | [] -> expr_vars

let subst_lfind_vars_in_expr expr sigma =
  let rec aux (acc: string list) = function 
  | (Atom tag)::tl -> 
                      let mapped_expr, _ = try (Hashtbl.find sigma tag) with _ -> [],""
                      in if Int.equal (List.length mapped_expr) 0 then
                      (aux ((protect tag)::acc) tl)
                      else
                      (
                        let mapped_expr_str = 
                        match mapped_expr with
                          | [Atom v] -> v
                          | _ -> ("(" ^ (string_of_sexpr mapped_expr) ^ ")")
                        in (aux (mapped_expr_str::acc) tl)
                      )
                      
  | (Expr e)::tl ->
        let s =
          "(" ^
          (String.concat " " (aux [] e))
          ^ ")"
        in
        aux (s::acc) tl
  | [] -> (List.rev acc)
  in
  let str_expr = (aux [] expr)
  in String.concat " " str_expr