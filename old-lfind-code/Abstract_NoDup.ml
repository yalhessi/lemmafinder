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

let get_type_table (terms: (Sexp.t list) list) (p_ctx: proof_context) 
                   : (string, string) Hashtbl.t=
  let type_tbl = Hashtbl.create (List.length terms)
  in List.iter (fun term -> let typ = 
                                    try TypeUtils.get_type_of_exp p_ctx.env p_ctx.sigma term 
                                    with _ -> 
                                    (if Utils.contains (Sexp.string_of_sexpr term) "else"then "bool"
                                    else
                                    "")
                            in Hashtbl.replace type_tbl (string_of_sexpr term) typ
               )
               terms; type_tbl

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
  in 
  let atoms = if with_hyp
                    then List.append conc_atoms hyp_atoms
                    else conc_atoms
  in let expr_type_table = get_type_table (List.append conc_terms hypo_terms) p_ctxt
  in let atom_type_table = (update_type_table atoms p_ctxt (Hashtbl.create 100))
  in

  LogUtils.write_tbl_to_log expr_type_table "Terms Type table";
  LogUtils.write_tbl_to_log atom_type_table "Atoms Type table";
  
  let vars_str = List.map Names.Id.to_string p_ctxt.vars in
  let all_terms = if with_hyp 
                        then List.tl (List.append conc_terms (List.tl hypo_terms))
                        else List.tl (conc_terms)
  in let all_terms = add_heuristic_atoms atoms all_terms atom_type_table vars_str
  in 
  let terms = get_generalizable_terms all_terms expr_type_table atom_type_table
  in Log.debug (Consts.fmt "Size of terms list %d\n and Terms from the goal [%s]\n" (List.length terms) (List.fold_left (fun acc e -> acc ^ ";" ^ ((string_of_sexpr e))) "" terms));
  (* Added empty generalization for synthesizing from stuck state. *)
  let generalization_set = (sets terms)
  in let hypo_implies_conc = p_ctxt.goal
  in let all_type_table = Hashtbl.fold (fun k v acc -> Hashtbl.add acc k v; acc ) atom_type_table expr_type_table in 

  (* **************************************************************************************************************************** *)
  (* Convert more robust type table to string version for sake of simple modification right now. *)
  let new_typ_table = CoqAPI.get_types_and_terms_from_context p_ctxt in 
  let new_func_typ_table = CoqAPI.get_functions_from_context p_ctxt in 
  let my_gen_terms = CoqAPI.get_terms_to_generalize p_ctxt new_typ_table in
  (* let new_str_type_table = Hashtbl.create (Hashtbl.length new_typ_table) in
  Hashtbl.iter (fun x (y,_,_) -> Hashtbl.add new_str_type_table x (Utils.get_econstr_str p_ctxt.env p_ctxt.sigma y)) new_typ_table; *)
  let str_gen_terms = List.map Sexp.string_of_sexpr terms in
  let result_1 = List.fold_left (fun b x -> List.mem x str_gen_terms && b) true  my_gen_terms in
  let result_2 = List.fold_left (fun b x -> List.mem x my_gen_terms && b) true  str_gen_terms in
  if (result_2 && result_1)
    then print_endline "same generalizable subterms"
  else 
    (
      print_endline "original terms: ";
      List.iter print_endline str_gen_terms;
      print_endline "\nmy terms: ";
      List.iter print_endline my_gen_terms
    );
  (* **************************************************************************************************************************** *)

  (* Patch for the expr type table --> to get the correct polymorphic types for conjecture generation *)
  let get_from_new x = let (typ,_,_) = (Hashtbl.find new_typ_table x) in CoqAPI.string_of_econstr p_ctxt typ in
  let patched_expr_type_table = Hashtbl.copy expr_type_table in
  Hashtbl.iter (fun x y -> if Hashtbl.mem new_typ_table x then Hashtbl.replace patched_expr_type_table x (get_from_new x) else ()) expr_type_table;
  LogUtils.write_tbl_to_log patched_expr_type_table "Patched Expr Type table"; 

  let patched_all_type_table = Hashtbl.fold (fun k v acc -> Hashtbl.add acc k v; acc ) atom_type_table patched_expr_type_table in 

  let generalizations = Generalize_NoDup.construct_all_generalizations generalization_set patched_all_type_table conc_sexp hypo_sexps
  in let conjectures = (Generalize_NoDup.get_all_conjectures generalizations atom_type_table patched_expr_type_table p_ctxt) 
  (* let generalizations = Generalize_NoDup.construct_all_generalizations generalization_set all_type_table conc_sexp hypo_sexps
  in let conjectures = (Generalize_NoDup.get_all_conjectures generalizations atom_type_table expr_type_table p_ctxt) *)
  in
  Log.debug (Consts.fmt "Generalizations: \n%s\n" (List.fold_left (fun acc c -> acc ^ (LatticeUtils.construct_implications c.conjecture_str c.hyps) ^ "\n") "" conjectures));
  terms, conjectures