(* Uses functions from Utils.ml (Utils.contains) and ProofContext.ml *)

let string_of_econstr (p_ctxt : ProofContext.proof_context) (expr : Evd.econstr) : string =
  (Pp.string_of_ppcmds (Printer.pr_goal_concl_style_env p_ctxt.env p_ctxt.sigma expr))
  
let string_of_constr (p_ctxt : ProofContext.proof_context) (expr : Constr.t) : string =
  (Pp.string_of_ppcmds (Printer.safe_pr_constr_env p_ctxt.env p_ctxt.sigma expr))

(* This function is just copied from Utils.ml --> not super familar with how Retyping module works *)
let get_type_of_econstr env sigma econstr = Retyping.get_type_of ~lax:false ~polyprop:false env sigma econstr

(* FUNCTION DEF : check_hypothesis_is_not_type
   Input : proof context and hypothesis (directly from ProofContext.hyps)
   Output : boolean indicating if the hypothesis is a type *)
let check_hypothesis_is_not_type (p_ctxt : ProofContext.proof_context) (hyp : (Evd.econstr, Evd.econstr) Context.Named.Declaration.pt) : bool =
  let hyp_econstr = match hyp with
  | Context.Named.Declaration.LocalAssum(_,y) -> y
  | Context.Named.Declaration.LocalDef(_,_,y) -> y
  in (* Check that it is type *)
  let (_,sort) = Typing.sort_of p_ctxt.env p_ctxt.sigma hyp_econstr in
  if (Sorts.is_set sort || ProofContext.is_type sort) = false then true
  else 
    let hyp_constr = EConstr.to_constr Evd.empty hyp_econstr in (* Do we want to pass p_ctxt.sigma instead of Evd.empty? *)
    (Constr.isSort(hyp_constr) || Constr.isVar(hyp_constr)) || (not (Constr.isApp(hyp_constr)) && not(Constr.isInd(hyp_constr)))

(* FUNCTION DEF : get_types_in_econstr
   Input : proof context, list to accumlate types (initially empty), and the econstr to pull types from
   Output : (expr : econstr * type : econstr) list for the type of the expressions found in and including this
   econstr (does not include the function names found from application)*)
let rec get_types_in_econstr (p_ctxt : ProofContext.proof_context) (type_terms) (econstr : Evd.econstr) = 
  match Constr.kind (EConstr.to_constr p_ctxt.sigma econstr) with
  | App (func, args) -> (* App is a sub-term that we would want to include, then iterate arguments *)
    (
      let econstr_type = get_type_of_econstr p_ctxt.env p_ctxt.sigma econstr in 
      let tmp = (econstr, econstr_type) :: type_terms in 
      (* let args_list =  List.map EConstr.of_constr (func :: Array.to_list args) in  --> collect functions differently *)
      let args_list =  List.map EConstr.of_constr (Array.to_list args) in 
      List.fold_left (get_types_in_econstr p_ctxt) tmp args_list
    )
  | _ -> (* This just adds any types from the econster, might want to finetune later on (could require more iteration) 
     --> For example, maybe iterate over Lambda, Prod or LetIn kinds to get all types (haven't encountered yet)*)
    try 
      let econstr_type = get_type_of_econstr p_ctxt.env p_ctxt.sigma econstr in
      (econstr, econstr_type) :: type_terms 
    with _ -> type_terms

(* FUNCTION DEF : get_types_of_func_in_econstr (similar to function above but find functions not subterms)
   Input : proof context, list to accumlate functions (initially empty), and the econstr to pull functions from
   Output : (expr : econstr * type : econstr) list for the type of the functions found in this econstr*)
let rec get_types_of_func_in_econstr (p_ctxt : ProofContext.proof_context) (func_type_terms) (econstr : Evd.econstr) = 
  match Constr.kind (EConstr.to_constr p_ctxt.sigma econstr) with
  | App (func, args) -> (* App is a sub-term that we would want to include, then iterate arguments *)
    (
      let func_constr_type = get_type_of_econstr p_ctxt.env p_ctxt.sigma (EConstr.of_constr func) in 
      let tmp = ((EConstr.of_constr func), func_constr_type) :: func_type_terms in 
      let args_list =  List.map EConstr.of_constr (Array.to_list args) in
      List.fold_left (get_types_of_func_in_econstr p_ctxt) tmp args_list
    )
  | _ -> func_type_terms

(* FUNCTION DEF : get_hypothesis_types
   Input : proof context and hypothesis (directly from ProofContext.hyps)
   Output : (variable : Names.variable option * expression : econstr option * type : econstr) list from the
   different types found from the provided hypothesis (which corresponds to the Names.variable option) *)
let get_hypothesis_types (p_ctxt : ProofContext.proof_context) (hyp : (Evd.econstr, Evd.econstr) Context.Named.Declaration.pt) =
  let var, econstr = match hyp with
  | Context.Named.Declaration.LocalAssum(x, y) -> (Context.(x.binder_name), y)
  | Context.Named.Declaration.LocalDef(x, _, y) -> (Context.(x.binder_name), y)
  in let is_type = not (check_hypothesis_is_not_type p_ctxt hyp) in
  if is_type then [(Some var,None,econstr)] (* if type, just return that var (Names.variable) and its type (Evd.econstr)*)
  else 
    let tmp = (get_types_in_econstr p_ctxt [] econstr) in
    (List.map (fun (x,y) -> (Some var,Some x,y)) tmp)

(* FUNCTION DEF : get_hypothesis_func_types
   Input : proof context and hypothesis (directly from ProofContext.hyps)
   Output : (variable : Names.variable option * expression : econstr option * type : econstr) list from the
   different functions found from the provided hypothesis (which corresponds to the Names.variable option) *)
let get_hypothesis_func_types (p_ctxt : ProofContext.proof_context) (hyp : (Evd.econstr, Evd.econstr) Context.Named.Declaration.pt) =
  let var, econstr = match hyp with
  | Context.Named.Declaration.LocalAssum(x, y) -> (Context.(x.binder_name), y)
  | Context.Named.Declaration.LocalDef(x, _, y) -> (Context.(x.binder_name), y)
  in let is_type = not (check_hypothesis_is_not_type p_ctxt hyp) in
  if is_type then [] (* if type, just return that var (Names.variable) and its type (Evd.econstr)*)
  else 
    let tmp = (get_types_of_func_in_econstr p_ctxt [] econstr) in
    (List.map (fun (x,y) -> (Some var,Some x,y)) tmp)

(* FUNCTION DEF : get_functions_from_context 
   Input : proof context
   Output : a table with all of the functions found in the context
      --> Table format:
      [key = string expression] 
      [value = (type : Evd.econstr * func term : Evd.econstr option * hypo variable : Names.variable option)] *)
let get_functions_from_context (p_ctxt : ProofContext.proof_context) = 
  let hypo_func_types = List.concat (List.map (get_hypothesis_func_types p_ctxt) p_ctxt.hypotheses) in 
  let goal_func_types = (List.map (fun (x,y) -> (None,Some x,y)) (get_types_of_func_in_econstr p_ctxt [] (p_ctxt.goal))) in
  let all_func_types = goal_func_types @ hypo_func_types in
  let func_type_table = Hashtbl.create (List.length all_func_types) in
  let fill_func_table = 
    fun (hypo,expr,typ) -> 
      match expr with 
      | Some term -> ( let key = (string_of_econstr p_ctxt term) in
      if Hashtbl.mem func_type_table key then () else Hashtbl.add func_type_table key (typ,Some term,None) )
      | None -> match hypo with 
        | Some var -> ( let key = (Names.Id.to_string var) in
        if Hashtbl.mem func_type_table key then () else Hashtbl.add func_type_table key (typ,None,Some var) )
        | None -> print_endline "Type without being assigned to a variable -- add exception here" 
  in List.iter fill_func_table all_func_types; func_type_table

(* FUNCTION DEF : get_types_and_terms_from_context 
   Input : proof context
   Output : a table with all of the functions found in the context
      --> Table format:
      [key = string expression] 
      [value = (type : Evd.econstr * expression : Evd.econstr option * hypo variable : Names.variable option)] *)
let get_types_and_terms_from_context (p_ctxt : ProofContext.proof_context) =
  let hypo_types = List.concat (List.map (get_hypothesis_types p_ctxt) p_ctxt.hypotheses) in 
  let goal_types = (List.map (fun (x,y) -> (None,Some x,y)) (get_types_in_econstr p_ctxt [] (p_ctxt.goal))) in
  let all_types = goal_types @ hypo_types in
  let type_table = Hashtbl.create (List.length all_types) in
  let fill_table = 
    fun (hypo,expr,typ) -> 
      match expr with 
      | Some term -> ( let key = (string_of_econstr p_ctxt term) in
        if Hashtbl.mem type_table key then () else Hashtbl.add type_table key (typ,Some term,hypo) )
      | None -> match hypo with 
        | Some var -> ( let key = (Names.Id.to_string var) in
          if Hashtbl.mem type_table key then () else Hashtbl.add type_table key (typ,None,Some var) )
        | None -> print_endline "Type without being assigned to a variable -- add exception here"
  in List.iter fill_table all_types; type_table

(* FUNCTION DEF : get_terms_to_generalize
   Input : proof context and the types table
   Output : string list (corresponds to keys of the types table) that can be generalized *)
let get_terms_to_generalize (p_ctxt : ProofContext.proof_context) (table : (string, Evd.econstr * Evd.econstr option * Names.variable option) Hashtbl.t) =
  let results = ref [] in
  Hashtbl.iter
  (fun str (typ,expr,var) -> 
    let econstr = (EConstr.to_constr p_ctxt.sigma typ) in
    if (Constr.is_Set econstr || Constr.is_Prop econstr)
      then ()
      else match expr with
      | None -> ()
      | Some e -> let eeconstr = (EConstr.to_constr p_ctxt.sigma e) in 
      (* Some room for exploration here what do we want to generalize or include for generalization, for example variables *)
        if ((Constr.isApp eeconstr || Constr.isConstruct eeconstr) && (not (Constr.is_Type (EConstr.to_constr p_ctxt.sigma typ)))) (* Do we want to include varaibles for generalization ? *)
        then (results := str :: !results)
        else ())
  table;
  (* This part checks to make sure that we are generalizing something within the goal state *)
  let goal_str = string_of_econstr p_ctxt p_ctxt.goal in
  List.filter (Utils.contains goal_str) !results
