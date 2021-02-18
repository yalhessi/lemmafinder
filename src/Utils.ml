
let parse_constr = Pcoq.parse_string Pcoq.Constr.constr;;

let str_to_constr str = (parse_constr str)

(* 
We assume that we are in a context with well-defined types, so we use Retyping instead of Typing. 
We can set lax to true if we dont want error to be thrown in case of a type error
*)
let get_type_of_exp env sigma exp = 
  let (sigma, t) = Constrintern.interp_constr_evars env sigma exp in
  let typ = Retyping.get_type_of ~lax:false env sigma t
  in typ

let get_str_of_pp pp_expr : string= 
    Pp.string_of_ppcmds pp_expr

let get_expr_str env sigma expr : string= 
  "(" ^ (get_str_of_pp (Printer.pr_goal_concl_style_env env sigma expr)) ^ ")"

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

let rec get_return_type acc fun_type =
    match fun_type with
    | (Sexp.Atom n):: [] -> n
    | (Sexp.Atom n):: tl -> get_return_type acc tl
    | (Sexp.Expr e):: tl -> let head_acc = get_return_type acc e
                            in get_return_type head_acc tl
    | [] -> acc