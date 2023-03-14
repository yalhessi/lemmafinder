exception Invalid_Env of string

let cons_uniq xs x = if List.mem x xs then xs else x :: xs

let dedup_list xs = List.rev (List.fold_left cons_uniq [] xs)

let parse_constr = Pcoq.parse_string Pcoq.Constr.constr;;

let str_to_constr str = (parse_constr str)

let strip str = 
  let str = Str.replace_first (Str.regexp "^ +") "" str in
  Str.replace_first (Str.regexp " +$") "" str

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

let get_func_full_str f : string =
  if not(Constr.isApp f) then (get_constr_str Environ.empty_env Evd.empty f)
  else
  let (f, args) = Constr.destApp f in
  let (name,_) = Constr.destConst f in
  "(@" ^ (Names.Constant.modpath name |> Names.ModPath.to_string) ^ "." ^ (Names.Constant.label name |> Names.Label.to_string) ^ " " ^ String.concat " " (List.map (get_constr_str Environ.empty_env Evd.empty) (Array.to_list args)) ^ ")"
  
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

let string_of_sexp_list elem =
"[" ^ (List.fold_left (fun accl e -> (Sexp.string_of_sexpr e) ^ ";" ^ accl) "" elem) ^ "]"

let econstr_to_constr x = EConstr.to_constr Evd.empty x

let forall_in_hyp hyp =
  match hyp with
  | Context.Named.Declaration.LocalAssum(x, y) -> Constr.isProd(econstr_to_constr y) (* forall *)
  | _ -> raise (Failure "Unsupported hypothesis type")

let rec get_vars_in_constr env sigma constr = 
  print_endline ("getting vars from: " ^ (get_constr_str env sigma constr));
  match Constr.kind constr with
  | Var(v) -> [constr]
  | Cast(ty1,ck,ty2) -> get_vars_in_constr env sigma ty1 @ get_vars_in_constr env sigma ty2
  | Prod(na, ty, c) -> get_vars_in_constr env sigma ty @ get_vars_in_constr env sigma c 
  | Lambda(na,ty,c) -> get_vars_in_constr env sigma ty @ get_vars_in_constr env sigma c
  | LetIn (na,b,ty,c) -> get_vars_in_constr env sigma b @ get_vars_in_constr env sigma ty @ get_vars_in_constr env sigma c
  | App(f,args) -> get_vars_in_constr env sigma f @ List.concat (List.map (fun arg -> get_vars_in_constr env sigma arg) (Array.to_list args))
  | Case(ci, p, c, bl) -> get_vars_in_constr env sigma c @ List.concat (List.map (fun e -> get_vars_in_constr env sigma e) (Array.to_list bl))
  | Rel(_) | Meta(_) | Evar(_) | Sort(_)  | Ind(_,_) | Const(_,_) | Construct(_,_) | Fix(_,_) | CoFix(_,_) | Proj(_,_) | Int(_) | Float(_) -> []

let get_vars_in_econstr env sigma econstr = 
  econstr_to_constr econstr |> get_vars_in_constr env sigma |> dedup_list

let rec get_funcs_in_constr env sigma constr = 
  (* let constr_goal = (econstr_to_constr expr) *)
  match Constr.kind constr with
  | Cast(ty1,ck,ty2) -> get_funcs_in_constr env sigma ty1 @ get_funcs_in_constr env sigma ty2
  | Prod(na, ty, c) -> get_funcs_in_constr env sigma ty @ get_funcs_in_constr env sigma c 
  | Lambda(na,ty,c) -> get_funcs_in_constr env sigma ty @ get_funcs_in_constr env sigma c
  | LetIn (na,b,ty,c) -> get_funcs_in_constr env sigma b @ get_funcs_in_constr env sigma ty @ get_funcs_in_constr env sigma c
  | App(f,args) -> 
    if (Constr.isConst f) && Array.exists (Constr.isVar) args 
    then
      [Constr.mkApp(f, Array.sub args 0 1)] @ List.concat (List.map (fun arg -> get_funcs_in_constr env sigma arg) (Array.to_list args))
      (* polymorphic functions *)
    else
      get_funcs_in_constr env sigma f @ List.concat (List.map (fun arg -> get_funcs_in_constr env sigma arg) (Array.to_list args))
  | Const(c,u) -> (* needed for zero-arg defintions *) [constr]
  | Case(ci, p, c, bl) -> get_funcs_in_constr env sigma c @ List.concat (List.map (fun e -> get_funcs_in_constr env sigma e) (Array.to_list bl))
  | Rel(_) | Var(_) | Meta(_) | Evar(_) | Sort(_)  | Ind(_,_) | Construct(_,_) | Fix(_,_) | CoFix(_,_) | Proj(_,_) | Int(_) | Float(_) -> []
  
let get_funcs_in_econstr env sigma econstr = 
  econstr_to_constr econstr |> get_funcs_in_constr env sigma |> dedup_list 
  
let get_env_var env_var : string =
  let env = Unix.environment ()
  in Array.fold_left (fun path p -> let p_list = Array.of_list(String.split_on_char '=' p)
                                    in let var = (try (Array.get p_list 0) with Invalid_argument _ -> "")
                                    in let var_path = try (Array.get p_list 1) with Invalid_argument _ -> ""
                                    in if String.equal var env_var then var_path else path
                     )
                     "" env

let get_modules file_name : string list =
  (* let cmd = "grep \"Require Import\" " ^ file_name
  in let modules = FileUtils.run_cmd cmd
  in modules *)
  []
   (* List.fold_left (fun acc m-> (List.nth (String.split_on_char ' ' m) 1)::acc) [] modules *)

let gen_rand_str length =
let gen() = match Random.int(26+26+10) with
    n when n < 26 -> int_of_char 'a' + n
  | n when n < 26 + 26 -> int_of_char 'A' + n - 26
  | n -> int_of_char '0' + n - 26 - 26 in
let gen _ = String.make 1 (char_of_int(gen())) in
String.concat "" (Array.to_list (Array.init length gen))

let slice_list (start_i: int) (end_i: int) (lst: 'a list) = 
  let _, slice = List.fold_right (fun e (index, acc) -> 
                                  let n_acc = if index >= start_i && index <= end_i
                                              then e :: acc
                                              else acc
                                  in index + 1, n_acc
                                 ) lst (0,[])
  in slice

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

  if String.equal !Consts.synthesizer "myth" then
  (
    let synthesizer_path = get_env_var "MYTH"
    in if String.equal synthesizer_path "" then raise (Invalid_Env "Synthesizer path not set!")
    else 
    Consts.synthesizer_path := synthesizer_path;
    
    let rewriter_path = get_env_var Consts.rewriter
    in if String.equal rewriter_path "" then raise (Invalid_Env "AST rewriter path not set!")
    else Consts.rewriter_path := rewriter_path;
  
    let coqofocaml_path = get_env_var "COQOFOCAML"
    in if String.equal coqofocaml_path "" then raise (Invalid_Env "COQOFOCAML path not set!")
    else Consts.coq_of_ocaml_path := coqofocaml_path;
  );

  let lfind_path = get_env_var "LFIND"
  in if String.equal lfind_path "" then raise (Invalid_Env "LFIND SRC path not set!")
  else Consts.lfind_path := if lfind_path.[(String.length lfind_path) -1] = '/' 
                            then lfind_path
                            else lfind_path ^ "/";