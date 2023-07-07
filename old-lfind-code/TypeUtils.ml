let get_type_str typ env sigma = Utils.get_str_of_pp 
                                  (Printer.pr_econstr_env env sigma typ)

let rec get_parametric_type exp =
  match exp with
  | [] -> ""
  | (Sexp.Atom f)::tl -> if Utils.contains f "@"
                    then (match tl with
                    | Atom t :: _ -> t
                    | (Expr e) :: _ -> Sexp.string_of_sexpr e)
                    else get_parametric_type tl
  | (Expr e) :: tl -> let t = get_parametric_type e
                      in if String.equal t "" then get_parametric_type tl else t

let rec get_type_variable typ type_pos=
  match typ with
  | [Sexp.Expr [Atom "forall"; Atom t; Atom ":"; Atom "Type,"; _ ; _]] -> t, 1
  | Expr [Atom t; Atom ":"; Atom "Type"] :: tl -> t, type_pos
  | (Atom _) :: tl -> get_type_variable tl (type_pos + 1)
  | (Sexp.Expr e):: tl -> 
                          let head_type, head_count = get_type_variable e type_pos
                          in if String.equal head_type ""
                          then get_type_variable tl (head_count + 1)
                          else head_type, head_count
  | [] -> "", type_pos

let type_subst typ type_var typ_pos exp =
  let parametric_type = get_parametric_type exp
  in (let rec aux i acc = function
  | (Sexp.Atom tag)::tl ->
                          let new_tag = 
                            if String.equal tag type_var 
                              then parametric_type 
                              else tag
                          in aux i ((new_tag)::acc) tl
  | (Expr e)::tl ->
      let s =
         (String.make i ' ') ^ "(" ^
        (String.concat " " (aux (succ i) [] e))
        ^ ")"
      in
      aux i (s::acc) tl
  | [] -> (List.rev acc)
  in
  String.concat "\n" (aux 0 [] (Sexp.of_string typ)))

(* 
We assume that we are in a context with well-defined types, 
so we use Retyping instead of Typing. 
We can set lax to true if we dont want error to be thrown in case of a type error
*)
let get_type_of_exp env sigma exp =
  let exp_constr = (Utils.str_to_constr (Sexp.string_of_sexpr exp))
  in let (sigma, t) = Constrintern.interp_constr_evars env sigma exp_constr in
  let typ = Retyping.get_type_of ~lax:false ~polyprop:false env sigma t
  in let typ_str = get_type_str typ env sigma
  in 
    begin
      let type_var, typ_pos = get_type_variable (Sexp.of_string typ_str) 0
      in 
          if String.equal type_var "" then typ_str
          else (type_subst typ_str type_var typ_pos exp)
    end

let get_type_of_atom env sigma atom =
  let exp_constr = (Utils.str_to_constr atom)
  in let (sigma, t) = Constrintern.interp_constr_evars env sigma exp_constr in
  let typ = 
            try Retyping.get_type_of ~lax:false ~polyprop:false env sigma t
            with _ -> let (sigma, typ) = Typing.type_of env sigma t in
                      typ
  in
  let typ_str = get_type_str typ env sigma
  in if Utils.contains typ_str "(" then (String.sub typ_str 1 (String.length typ_str - 2)) else typ_str

let rec get_return_type acc fun_type =
  match fun_type with
  | (Sexp.Atom n)::[] -> n
  | (Sexp.Atom n):: tl -> if Utils.contains n "," then
                          (Sexp.string_of_sexpr tl)
                          else get_return_type acc tl
  | (Sexp.Expr e):: tl -> let head_acc = get_return_type acc e
                          in get_return_type head_acc tl
  | [] -> acc

let get_type_name env sigma (typ : EConstr.t) : string =
  match Constr.kind (Utils.econstr_to_constr typ) with
  | Ind (_, _) -> Utils.get_econstr_str env sigma typ
  | App(f, args) -> Utils.get_constr_str env sigma f
  | _ -> raise (Failure "Unexpected type")

let derive_typ_quickchick (p_ctxt : ProofContext.proof_context) (typ : EConstr.t) : string= 
  let typ_constr = Utils.econstr_to_constr typ in
  if Constr.isSort(typ_constr) || Constr.isVar(typ_constr) then ""
  else if not (Constr.isApp(typ_constr)) && not(Constr.isInd(typ_constr)) then
    raise (Failure "Unexpected type")
  else
  let typ_name = get_type_name p_ctxt.env p_ctxt.sigma typ in
  let file_name = Consts.fmt "%s/show_%s.v" p_ctxt.dir typ_name in
  if Sys.file_exists file_name then
    String.concat "\n" (FileUtils.read_file file_name |> List.rev)
  else
  Consts.fmt ("Derive Show for %s.\n
              Derive Arbitrary for %s.\n
              Instance Dec_Eq_%s : Dec_Eq %s.\n
              Proof. dec_eq. Qed.\n")
              typ_name typ_name typ_name typ_name