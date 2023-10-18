exception Invalid_Env of string

let cons_uniq xs x = if List.mem x xs then xs else x :: xs

let dedup_list xs = List.rev (List.fold_left cons_uniq [] xs)

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

let get_econstr_str env sigma expr : string =
  (get_str_of_pp (Printer.pr_goal_concl_style_env env sigma expr))
  
let get_constr_str env sigma expr : string =
  (get_str_of_pp (Printer.safe_pr_constr_env env sigma expr))

let get_func_full_str sigma f : string =
  if not(EConstr.isApp sigma f) then (get_econstr_str Environ.empty_env Evd.empty f)
  else
  let (f, args) = EConstr.destApp sigma f in
  let (name,_) = EConstr.destConst sigma f in
  "(@" ^ (Names.Constant.modpath name |> Names.ModPath.to_string) ^ "." ^ (Names.Constant.label name |> Names.Label.to_string) ^ " " ^ String.concat " " (List.map (get_econstr_str Environ.empty_env Evd.empty) (Array.to_list args)) ^ ")"
  
let get_sexp_compatible_expr_str env sigma expr : string = 
  "(" ^ (get_exp_str env sigma expr) ^ ")"

let get_term_count terms exp =
    List.fold_left (fun acc (e, count) -> if Sexp.equal e exp then (count) else acc) 0 terms

let add_term (acc : (Sexp.t list * int) list) (term: Sexp.t list): (Sexp.t list * int) list * int =
    let count = (get_term_count acc term) + 1
    in List.append acc [(term, count)], count

let add_term_remove_dup (acc : Sexp.t list list)
                        (term: Sexp.t list): 
                        (Sexp.t list) list =
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

let econstr_to_constr x = EConstr.to_constr Evd.empty x

let forall_in_hyp hyp =
  match hyp with
  | Context.Named.Declaration.LocalAssum(x, y) -> Constr.isProd(econstr_to_constr y) (* forall *)
  | _ -> raise (Failure "Unsupported hypothesis type")

let get_sort_of_econstr env sigma econstr = 
  Retyping.get_sort_of ~polyprop:false env sigma econstr

let get_type_of_econstr env sigma econstr = 
  Retyping.get_type_of ~lax:false ~polyprop:false env sigma econstr

let is_type_type env sigma econstr =
  let typ = get_type_of_econstr env sigma econstr in
  EConstr.isType sigma typ

let is_type_var env sigma econstr =
  EConstr.isVar sigma econstr && is_type_type env sigma econstr
  
let rec get_funcs_in_econstr env sigma econstr = 
  match EConstr.kind sigma econstr with
  | Cast(ty1,ck,ty2) -> get_funcs_in_econstr env sigma ty1 @ get_funcs_in_econstr env sigma ty2
  | Prod(na, ty, c) -> get_funcs_in_econstr env sigma ty @ get_funcs_in_econstr env sigma c 
  | Lambda(na,ty,c) -> get_funcs_in_econstr env sigma ty @ get_funcs_in_econstr env sigma c
  | LetIn (na,b,ty,c) -> get_funcs_in_econstr env sigma b @ get_funcs_in_econstr env sigma ty @ get_funcs_in_econstr env sigma c
  | App(f,args) -> 
    if (EConstr.isConst sigma f) && Array.exists (is_type_var env sigma) args 
    then
      [EConstr.mkApp(f, Array.sub args 0 1)] @ List.concat (List.map (fun arg -> get_funcs_in_econstr env sigma arg) (Array.to_list args))
      (* polymorphic functions *)
    else
      get_funcs_in_econstr env sigma f @ List.concat (List.map (fun arg -> get_funcs_in_econstr env sigma arg) (Array.to_list args))
  | Const(c,u) -> (* needed for zero-arg defintions *) [econstr]
  | Case(ci, p, c, bl) -> get_funcs_in_econstr env sigma c @ List.concat (List.map (fun e -> get_funcs_in_econstr env sigma e) (Array.to_list bl))
  | Rel(_) | Var(_) | Meta(_) | Evar(_) | Sort(_)  | Ind(_,_) | Construct(_,_) | Fix(_,_) | CoFix(_,_) | Proj(_,_) | Int(_) | Float(_) -> []
  
let get_env_var env_var : string =
  let env = Unix.environment ()
  in Array.fold_left (fun path p -> let p_list = Array.of_list(String.split_on_char '=' p)
                                    in let var = (try (Array.get p_list 0) with Invalid_argument _ -> "")
                                    in let var_path = try (Array.get p_list 1) with Invalid_argument _ -> ""
                                    in if String.equal var env_var then var_path else path
                     )
                     "" env

let gen_rand_str length =
let gen() = match Random.int(26+26+10) with
    n when n < 26 -> int_of_char 'a' + n
  | n when n < 26 + 26 -> int_of_char 'A' + n - 26
  | n -> int_of_char '0' + n - 26 - 26 in
let gen _ = String.make 1 (char_of_int(gen())) in
String.concat "" (Array.to_list (Array.init length gen))

let vars_with_types_to_str (vars_with_types : (string * string) list) : string =
  String.concat " " (List.map (fun (var, ty) -> "(" ^ var ^ " : " ^ ty ^ ")") vars_with_types)

let cpu_count () = 
  try 
    (match Sys.os_type with 
    | "Win32" -> int_of_string (Sys.getenv "NUMBER_OF_PROCESSORS") 
    | _ ->
        (
          let i = Unix.open_process_in "getconf _NPROCESSORS_ONLN" in
          let close () = ignore (Unix.close_process_in i) in
          try Scanf.fscanf i "%d" (fun n -> close (); n) with e -> close (); raise e
        )
    )
  with  _ -> 1
  
let env_setup () =
  let prover_path = get_env_var Consts.prover
  in
  if String.equal prover_path "" then raise (Invalid_Env "Prover path not set!")
  else Consts.prover_path := if prover_path.[(String.length prover_path) -1] = '/' 
                           then prover_path
                           else prover_path ^ "/";
  let lfind_path = get_env_var "LFIND"
  in if String.equal lfind_path "" then raise (Invalid_Env "LFIND SRC path not set!")
  else Consts.lfind_path := if lfind_path.[(String.length lfind_path) -1] = '/' 
                            then lfind_path
                            else lfind_path ^ "/";