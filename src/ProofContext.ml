type proof_context = 
  {
    env: Environ.env;
    sigma: Evd.evar_map;
    hypotheses : EConstr.named_context;
    goal : EConstr.t;
    vars : Names.variable list;
    samples :  string list list;
    fname: string;
    dir: string;
    full_context: string;
    namespace: string;
    declarations: string;
    proof_name: string;
    funcs: Constr.t list;
    modules: string list;
    types: EConstr.t list;
    theorem : string;
    all_vars: Names.variable list;
    original_dir: string;
  }

type coq_context = 
  {
    env : Environ.env;
    sigma : Evd.evar_map;
  }

let hyps_to_string_list env sigma hyps = 
  Utils.get_hyps_strl hyps env sigma

let hyps_to_string env sigma hyps = 
  let hyps_str = Utils.get_hyps_strl hyps env sigma in
  List.fold_left (fun acc h ->  acc ^ "\n" ^ h) "" hyps_str
let goal_to_string env sigma goal = 
  Utils.get_sexp_compatible_expr_str env sigma goal

let to_string (p_ctxt : proof_context) = 
  let hyps_str = hyps_to_string p_ctxt.env p_ctxt.sigma p_ctxt.hypotheses
  in hyps_str ^ "\n" ^ "=========================" ^ (goal_to_string p_ctxt.env p_ctxt.sigma p_ctxt.goal)
  
let get_fname full_context =
  let library = List.hd (String.split_on_char '\n' full_context)
  in let fname = List.hd (List.rev (String.split_on_char '.' library))
  in fname

let get_declarations dir fname =
  let lines = FileUtils.read_file (dir ^ "/" ^ fname ^ ".v")
  in List.fold_right (fun line acc -> 
                            let is_comment = Utils.contains line "*"
                            in let is_quickchick = Utils.contains line "QuickChick"
                            in if (not is_comment) && (not is_quickchick) && (Utils.contains line "Import")
                               then acc ^ "\n" ^ line
                               else acc
                     ) lines ""

let get_dir paths =
List.fold_left (fun (namespace, dir) path ->
                  let path_str = (Utils.get_str_of_pp (Loadpath.pp (path)))
                  in let is_contains = Utils.contains path_str "Coq."
                  in if is_contains || not (String.equal dir "") 
                  then (namespace, dir)
                  else
                  (
                      let pathl = (String.split_on_char ' ' path_str)
                      in let namespace = List.hd pathl
                      in let dir = List.hd (List.rev pathl)
                      in (namespace, dir)
                  )
                ) ("", "") paths

let get_theorem proof_name dir fname = 
  let content = List.rev (FileUtils.read_file (Consts.fmt "%s/%s.v" dir fname))
  in List.fold_left (
                      fun acc l ->
                      if (Utils.contains l ("Lemma " ^ proof_name)) || (Utils.contains l ("Theorem " ^ proof_name))
                      then l
                      else acc
                    ) "" content

let get_proof_name () =
  let pstate = match Vernacstate.Proof_global.get_pstate () with Some ps -> ps | _ -> (raise (Invalid_argument "proof state"))
  in let pdata = Proof.data (Proof_global.get_proof pstate) in
  (Names.Id.to_string (pdata.name))

let is_type s = 
  match Sorts.family s with
  | InType -> true
  | _ -> false
  
let get_vars env sigma hyps  =
  let var_hyps = List.filter (fun hyp -> match hyp with
  | Context.Named.Declaration.LocalAssum(x, y) -> 
    let (sigma', s) = Typing.sort_of env sigma y in
    Sorts.is_set s || is_type s
  | _ -> raise(Failure "Unsupported assumption") ) hyps in
  List.map (fun hyp -> match hyp with
  | Context.Named.Declaration.LocalAssum(x, y) ->  x.binder_name
  | _ -> raise(Failure "Unsupported assumption")) var_hyps

let get_var_types env sigma hyps  =
  let var_hyps = List.filter (fun hyp -> match hyp with
  | Context.Named.Declaration.LocalAssum(x, y) -> 
    let (sigma', s) = Typing.sort_of env sigma y in
    Sorts.is_set s || is_type s
  | _ -> raise(Failure "Unsupported assumption") ) hyps in
  List.map (fun hyp -> match hyp with
  | Context.Named.Declaration.LocalAssum(x, y) ->  (x.binder_name, y)
  | _ -> raise(Failure "Unsupported assumption")) var_hyps

let get_types env sigma hyps  =
  let var_hyps = List.filter (fun hyp -> match hyp with
  | Context.Named.Declaration.LocalAssum(x, y) -> 
    let (sigma', s) = Typing.sort_of env sigma y in
    Sorts.is_set s || is_type s
  | _ -> raise(Failure "Unsupported assumption") ) hyps in
  List.map (fun hyp -> match hyp with
  | Context.Named.Declaration.LocalAssum(x, y) -> y
  | _ -> raise(Failure "Unsupported assumption")) var_hyps |> Utils.dedup_list


let get_curr_state_lemma p_ctxt : string = 
  let lemma = Consts.lfind_lemma in
  let vars = List.map Names.Id.to_string p_ctxt.vars in
  let vars_str = "forall " ^ String.concat " " vars in
  let conc = (Utils.get_exp_str p_ctxt.env p_ctxt.sigma p_ctxt.goal) in
  let hyps = p_ctxt.hypotheses in
  let hyps_str = List.map (fun hyp -> match hyp with 
    | Context.Named.Declaration.LocalAssum(x, y) -> 
      "(" ^ Names.Id.to_string (x.binder_name) ^ ":" ^ (Utils.get_exp_str p_ctxt.env p_ctxt.sigma y) ^ ")"
    | _ -> raise(Failure "Unsupported assumption")) hyps |> String.concat " "  in
  if List.length hyps = 0 then
    Consts.fmt "Lemma %s:%s.\nAdmitted." Consts.lfind_lemma conc
  else
    Consts.fmt "Lemma %s %s:%s.\nAdmitted." Consts.lfind_lemma hyps_str conc
  
let construct_proof_context gl =
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let hyps = Proofview.Goal.hyps gl |> List.rev (* hyps are in opposite order of coqide *) in
    let goal = Proofview.Goal.concl gl in
    let vars = get_vars env sigma hyps in
    let typs = get_types env sigma hyps in
    let goal_funcs = Utils.new_get_funcs_in_econstr env sigma goal in
    let hyp_funcs = List.map (fun (_,h) -> Utils.new_get_funcs_in_econstr env sigma h) (Utils.get_hyps hyps) in
    let all_funcs = List.concat (goal_funcs :: hyp_funcs) in
    let paths = Loadpath.get_load_paths ()
    in let namespace, dir = get_dir paths
    in let parent_dir, curr_dir = FileUtils.get_parent_curr_dir dir in
    let lfind_dir = parent_dir ^ "_lfind_" ^ curr_dir in
    Log.enable_debug (lfind_dir ^ Consts.debug_log_file);
    FileUtils.cp_dir dir (lfind_dir);    
    let full_context = Utils.get_str_of_pp (Prettyp.print_full_context env sigma)
    in let f_name = get_fname full_context
    in let declarations = get_declarations lfind_dir f_name
    in let proof_name = get_proof_name ()
    in let theorem = get_theorem proof_name lfind_dir f_name 
    in let p_ctxt = {
        env = env;
        sigma = sigma;
        theorem = theorem;
        hypotheses = hyps; 
        goal = goal; 
        samples = [];
        dir = lfind_dir;
        full_context = full_context;
        fname = f_name;
        vars = vars;
        namespace = List.hd (String.split_on_char '\n' namespace);
        declarations = declarations;
        proof_name = proof_name;
        funcs = all_funcs;
        modules = [];
        types = typs;
        all_vars = vars;
        original_dir = dir;
       }
    in let c_ctxt = {env = env; sigma = sigma} 
    in p_ctxt, c_ctxt
                  