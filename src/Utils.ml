
let parse_constr = Pcoq.parse_string Pcoq.Constr.constr;;

let str_to_constr str = (parse_constr str)

let contains s1 s2 =
  let re = Str.regexp_string s2 in
  try 
      ignore (Str.search_forward re s1 0); 
      true
  with Not_found -> false

let get_str_of_pp pp_expr : string= 
    Pp.string_of_ppcmds pp_expr

let get_exp_str env sigma expr : string =
  (get_str_of_pp (Printer.pr_goal_concl_style_env env sigma expr))

let get_sexp_compatible_expr_str env sigma expr : string = 
  "(" ^ (get_exp_str env sigma expr) ^ ")"

let get_term_count terms exp =
    List.fold_left (fun acc (e, count) -> if Sexp.equal e exp then (count) else acc) 0 terms

let add_term (acc : (Sexp.t list * int) list) (term: Sexp.t list): (Sexp.t list * int) list * int =
    let count = (get_term_count acc term) + 1
    in List.append acc [(term, count)], count

let add_term_remove_dup (acc : Sexp.t list list) (term: Sexp.t list): (Sexp.t list) list =
  let exists = List.exists (fun e -> Sexp.equal e term) acc
  in if exists then acc else List.append acc [term]

let next_val counter = 
  fun () ->
    counter := (!counter) + 1;
    !counter

let get_hyps hyps =
  List.map
    (function
    | Context.Named.Declaration.LocalAssum(x, y) -> (Context.(x.binder_name), y)
    | Context.Named.Declaration.LocalDef(x, _, y) -> (Context.(x.binder_name), y))
    hyps

let get_hyps_strl hyps env sigma =
  List.fold_left (fun acc (v, hyp) -> 
                              let var_str = (Names.Id.to_string v)
                              in let regex_ih  = Str.regexp "IH*"
                              in let regex_H = Str.regexp "H*"
                              in let is_match = 
                                          Str.string_match regex_ih var_str 0
                              in (if is_match 
                                  then (get_sexp_compatible_expr_str env sigma hyp)::acc
                                  else acc)
                 ) [] (get_hyps hyps)

let string_of_sexp_list elem =
"[" ^ (List.fold_left (fun accl e -> (Sexp.string_of_sexpr e) ^ ";" ^ accl) "" elem) ^ "]"

let econstr_to_constr x = EConstr.to_constr Evd.empty x

let add_var acc var =
  let var_exists = List.exists (fun e -> String.equal e var) acc
  in if var_exists then acc else (var :: acc)

let get_vars_in_expr expr =
  let constr_goal = (econstr_to_constr expr)
  in let rec aux constr_goal (vars : string list) =
      match Constr.kind constr_goal with
      | Var v -> add_var vars (Names.Id.to_string v)
      | Cast (ty1,ck,ty2) ->  let ty1_vars = aux ty1 vars
                              in aux ty2 ty1_vars
      | Prod (na,ty,c)    ->  let ty_vars = aux ty vars
                              in aux c ty_vars
      | Lambda (na,ty,c)  ->  let ty_vars = aux ty vars
                              in aux c ty_vars
      | LetIn (na,b,ty,c) ->  let ty_vars = aux ty vars
                              in aux c ty_vars
      | App (f,args)      ->  let f_vars = aux f vars
                              in let args_vars = (vars_of_constrarray args)
                              in List.fold_left 
                                  (fun acc v -> add_var acc v) f_vars args_vars
      | Proj (p,c)        ->  aux c vars
      | Case (ci,p,c,bl)  ->  aux c vars
      | _ -> vars
and vars_of_constrarray a : string list =
    List.fold_left (fun acc elem -> List.append acc (aux elem acc)) [] (Array.to_list a)
in aux constr_goal []

let get_env_var env_var : string =
  let env = Unix.environment ()
  in Array.fold_left (fun path p -> let p_list = Array.of_list(String.split_on_char '=' p)
                                    in let var = (try (Array.get p_list 0) with Invalid_argument _ -> "")
                                    in let var_path = try (Array.get p_list 1) with Invalid_argument _ -> ""
                                    in if String.equal var env_var then var_path else path
                     )
                     "" env