open Utils
open ProofContext
open LatticeUtils
open Sexp

let rec collect_terms_no_dup (acc: (Sexp.t list) list)
                             (atoms : string list)
                             (sexp: Sexp.t list) 
                             : ((Sexp.t list) list) * string list =
  match sexp with
  | (Atom a) :: tl -> let updated_atoms = if List.mem a atoms 
                                          then atoms else (a :: atoms)
                         in collect_terms_no_dup acc updated_atoms tl
  | (Expr head) :: tl -> let new_acc = (add_term_remove_dup acc head)
                         in 
                         (* We do not want to further collect atoms from a function
                         unroll in the proof state. *)
                         if contains (Sexp.string_of_sexpr [(List.hd head)]) "fix" then
                         collect_terms_no_dup new_acc atoms tl
                         else 
                         (
                           let head_terms, head_atoms = collect_terms_no_dup new_acc atoms head
                           in collect_terms_no_dup head_terms head_atoms tl
                         )
  | [] -> acc, atoms

let get_type_table (terms: (Sexp.t list) list) (c_ctx: coq_context) 
                   : (string, string) Hashtbl.t=
  let type_tbl = Hashtbl.create (List.length terms)
  in List.iter (fun term -> let typ = 
                                    try TypeUtils.get_type_of_exp c_ctx.env c_ctx.sigma term 
                                    with _ -> 
                                    (if Utils.contains (Sexp.string_of_sexpr term) "else"then "bool"
                                    else
                                    "")
                            in Hashtbl.replace type_tbl (string_of_sexpr term) typ
               )
               terms; type_tbl

let powerset_to_string (p_set: (Sexp.t list) list list) : string = 
  List.fold_left (fun (acc: string) (elem: (Sexp.t list) list) 
                      -> let elem_str = "[" ^ (List.fold_left (fun accl e -> (string_of_sexpr e) ^ ";" ^ accl) "" elem) ^ "]"
                          in acc ^ "\n" ^ elem_str
                  ) "" p_set

let get_generalizable_terms (all_terms: Sexp.t list list)
                            (expr_type_table: (string, string) Hashtbl.t)
                            (atom_type_table: (string, string) Hashtbl.t)
                            : Sexp.t list list =
  (*
    Input: Takes in atom and term/expr type tables and all possible terms + atom from hyp and goal
    Output: Returns a list of valid terms + atoms that can be generalized 
  *)
  List.fold_left (fun acc term -> let term_type = try 
                                                     Hashtbl.find expr_type_table (string_of_sexpr term)
                                                  with _ ->
                                                     try Hashtbl.find atom_type_table (string_of_sexpr term) with _ -> ""
                                  in let return_type = try TypeUtils.get_return_type "" (of_string term_type) with _ -> term_type
                                  (* If it is type `type` like nat, we do not want to generalize it and if the type is
                                     ill-formed i.e. empty we do not want to generalize it. 
                                  *)
                                  in if (String.equal return_type "Type") || (String.equal return_type "")
                                     then acc
                                     else (add_term_remove_dup acc term)
                 ) [] all_terms

let add_heuristic_atoms (all_atoms: string list)
                        (current_terms: Sexp.t list list) 
                        (atom_type_table: (string, string) Hashtbl.t) 
                        (vars: string list) : Sexp.t list list=
  (* 
    Input: All atoms and terms from goal and hyps, type table and variables
    Output: List of constant atoms (i.e. have type Set)
  *)
  (* Get nil that are not polymorphic, if it is polymorphic we already capture them in the terms for generalization *)
  List.fold_left (fun acc a ->
            let is_var = List.exists (String.equal a) vars
            in let atom_type = try Hashtbl.find atom_type_table a with _ -> ""
            in
            let is_atom_type_set = try
                                      let atom_type_type = Hashtbl.find           atom_type_table atom_type 
                                      in
                                      Utils.contains atom_type_type "Set"
                                  with _ ->
                                  false
            in if (is_atom_type_set && (not is_var) && not (Utils.contains a "@"))
                                        then [Atom a]::acc 
                                        else acc
        ) current_terms all_atoms

let abstract (p_ctxt : proof_context) 
             (c_ctxt : coq_context) 
             : Sexp.t list list * conjecture list =
  (* 
    Input: proof and coq context
    Ouput: Tuple <generalized terms/expr, generalized conjectures>
  *)
  let with_hyp = false
  in let hypo_sexps = List.map (fun hyp -> Sexp.of_string hyp) (Utils.get_hyps_strl p_ctxt.hypotheses p_ctxt.env p_ctxt.sigma)
  in
  let conc_sexp = Sexp.of_string (ProofContext.goal_to_string p_ctxt.env p_ctxt.sigma p_ctxt.goal)
  in let conc_terms, conc_atoms = collect_terms_no_dup [] [] conc_sexp
  in let hypo_terms, hyp_atoms = List.fold_left 
                                  (fun (hyp_terms,hyp_atoms) hypo_sexp -> 
                                        let terms, atoms = (collect_terms_no_dup [] [] hypo_sexp)
                                        in List.append hyp_terms terms, List.append atoms hyp_atoms
                                  ) ([],[]) hypo_sexps
  in let atoms = if with_hyp
                    then List.append conc_atoms hyp_atoms
                    else conc_atoms
  in let expr_type_table = get_type_table (List.append conc_terms hypo_terms) c_ctxt
  in let atom_type_table = (update_type_table atoms c_ctxt (Hashtbl.create 100))
  in
  LogUtils.write_tbl_to_log expr_type_table "Terms Type table";
  LogUtils.write_tbl_to_log atom_type_table "Atoms Type table";
  
  let all_terms = if with_hyp 
                        then List.tl (List.append conc_terms (List.tl hypo_terms))
                        else List.tl (conc_terms)
  in let all_terms = add_heuristic_atoms atoms all_terms atom_type_table p_ctxt.vars
  in
  let terms = get_generalizable_terms all_terms expr_type_table atom_type_table
  in Log.debug (Consts.fmt "Size of terms list %d\n and Terms from the goal [%s]\n" (List.length terms) (List.fold_left (fun acc e -> acc ^ ";" ^ ((string_of_sexpr e))) "" terms));
  (* Added empty generalization for synthesizing from stuck state. *)
  let generalization_set = (sets terms)
  in let hypo_implies_conc = p_ctxt.goal
  in
  let all_type_table = Hashtbl.fold (fun k v acc -> Hashtbl.add acc k v; acc ) atom_type_table expr_type_table
  in let generalizations = Generalize_NoDup.construct_all_generalizations generalization_set all_type_table conc_sexp hypo_sexps
  in let conjectures = (Generalize_NoDup.get_all_conjectures generalizations atom_type_table expr_type_table p_ctxt)
  in
  Log.debug (Consts.fmt "Generalizations: \n%s\n" (List.fold_left (fun acc c -> acc ^ (LatticeUtils.construct_implications c.conjecture_str c.hyps) ^ "\n") "" conjectures));
  terms, conjectures