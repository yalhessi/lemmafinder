type proof_context = 
  {
    hypotheses : string list;
    goal : string;
    functions : string list;
    vars : string list;
    samples :  string list list;
    fname: string;
    dir: string;
    full_context: string;
    namespace: string;
    declarations: string;
    proof_name: string;
    funcs: string list;
    modules: string list;
    types: string list;
  }

type coq_context = 
  {
    env : Environ.env;
    sigma : Evd.evar_map;
  }

let hyp_to_string hyp = 
  List.fold_left (fun acc h ->  acc ^ "\n" ^ h) "" hyp

let to_string p_ctxt = 
  let hyp_str = hyp_to_string p_ctxt.hypotheses
  in hyp_str ^ "\n" ^ "=========================" ^ p_ctxt.goal
  
let get_fname full_context =
  let library = List.hd (String.split_on_char '\n' full_context)
  in let fname = List.hd (List.rev (String.split_on_char '.' library))
  in fname

let get_declarations dir fname =
  let lines = FileUtils.read_file (dir ^ "/" ^ fname ^ ".v")
  in List.fold_right (fun line acc -> 
                            let is_comment = Utils.contains line "*"
                            in if (not is_comment) && (Utils.contains line "Import")
                               then acc ^ "\n" ^ line
                               else acc
                     ) lines ""

let get_dir paths =
List.fold_left (fun (namespace, dir) path -> 
                  let path_str = (Utils.get_str_of_pp (Loadpath.pp (path)))
                  in let is_contains = Utils.contains path_str "coq"
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

let construct_proof_context gl =
    let pstate = match Vernacstate.Proof_global.get_pstate () with Some ps -> ps | _ -> (raise (Invalid_argument "proof state"))
    in let pdata = Proof.data (Proof_global.get_proof pstate)
    in let proof_name = (Names.Id.to_string (pdata.name))
    in let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let goal = Proofview.Goal.concl gl in
    let hyps = Proofview.Goal.hyps gl in
    let hyps_strl = Utils.get_hyps_strl hyps env sigma in
    let c_ctxt = {env = env; sigma = sigma}
    in let vars = Utils.get_vars_in_expr goal
    in let funcs = Utils.get_funcs_in_expr goal []
    in let hyp_funcs = List.fold_left 
                        (fun acc (_,h) -> (Utils.get_funcs_in_expr h acc)
                        ) funcs (Utils.get_hyps hyps)
    in let paths = Loadpath.get_load_paths ()
    in let namespace, dir = get_dir paths
    in let parent_dir, curr_dir = FileUtils.get_parent_curr_dir dir in
    let lfind_dir = parent_dir ^ "_lfind_" ^ curr_dir in
    Log.enable_debug (lfind_dir ^ Consts.debug_log_file);
    FileUtils.cp_dir dir (lfind_dir);    
    let full_context = Utils.get_str_of_pp (Prettyp.print_full_context env sigma)
    in let f_name = get_fname full_context
    in let declarations = get_declarations lfind_dir f_name
    in let p_ctxt = {
        hypotheses = hyps_strl; 
        goal = (Utils.get_sexp_compatible_expr_str env sigma goal); 
        functions = []; 
        samples = [];
        dir = lfind_dir;
        full_context = full_context;
        fname = f_name;
        vars = vars;
        namespace = List.hd (String.split_on_char '\n' namespace);
        declarations = declarations;
        proof_name = proof_name;
        funcs = hyp_funcs;
        modules = [];
        types = [];
       }
    in p_ctxt, c_ctxt
                  