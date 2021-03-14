open LatticeUtils
open ProofContext

let term_contains_gen_var term gen_vars =
  List.exists (fun gvar -> 
                   Utils.contains (Sexp.string_of_sexpr term) gvar
              ) gen_vars

let add_synthesis_term acc gen_vars term type_tbl =
  let term_type = try (Hashtbl.find type_tbl (Sexp.string_of_sexpr term)) with _ -> ""
  in let return_type = TypeUtils.get_return_type "" (Sexp.of_string term_type)
  in if String.equal return_type "Type"
    then acc 
    else 
        (let exists = List.exists (fun e -> Sexp.equal e term) acc
        in if exists 
          then acc
          else if term_contains_gen_var term gen_vars
                then acc
                else term :: acc)

let rec get_terms_to_synthesize (acc : Sexp.t list list) (conjecture: Sexp.t list)
                                (gen_vars: string list) type_tbl : Sexp.t list list =
  match conjecture with
  | (Atom a) :: tl -> get_terms_to_synthesize acc tl gen_vars type_tbl
  | (Expr head) :: tl -> let new_acc = (add_synthesis_term acc gen_vars head type_tbl)
                          in let head_terms = get_terms_to_synthesize new_acc head gen_vars type_tbl
                          in get_terms_to_synthesize head_terms tl gen_vars type_tbl
  | [] -> acc

let evaluate_generalized_expr conjecture examples p_ctxt =
  let no_lfind_vars = (List.length conjecture.lfind_vars)
  in List.fold_left (fun acc lvar -> 
                            let expr, _ = Hashtbl.find conjecture.sigma lvar
                            in let expr_output = (Evaluate.evaluate_coq_expr expr examples p_ctxt)
                            in (Hashtbl.add acc lvar expr_output);
                            acc
                     )
                 (Hashtbl.create no_lfind_vars) conjecture.lfind_vars

let add_conj_vars conj_vars vars lfind_vars var =
let is_exists_in_vars = List.exists (fun v -> String.equal v var) vars
in let is_exists_in_lfind_vars = List.exists (fun v -> String.equal v var) lfind_vars
in let is_dup = List.exists (fun v -> String.equal v var) conj_vars
in if (is_exists_in_vars || is_exists_in_lfind_vars) & not is_dup 
    then var :: conj_vars
    else conj_vars

let rec get_variables_except_expr conjecture expr conj_vars vars lfind_vars =
match conjecture with
| (Sexp.Atom v) :: tl -> 
                        let updated_vars = (add_conj_vars conj_vars vars lfind_vars v)
                        in get_variables_except_expr tl expr updated_vars vars lfind_vars
| (Sexp.Expr hd) :: tl -> 
                          if (Sexp.equal hd expr)
                          then
                            get_variables_except_expr tl expr conj_vars vars lfind_vars
                          else
                            (let head_vars = get_variables_except_expr hd expr conj_vars vars lfind_vars
                            in get_variables_except_expr tl expr head_vars vars lfind_vars)
| [] -> conj_vars

let get_type_vars (conjecture : conjecture) vars =
  let type_tbl = Hashtbl.create (List.length vars)
  in List.iter ( fun v -> let _, expr_type = try (Hashtbl.find conjecture.sigma v) 
                                          with _ -> [], ""
                                   in if String.equal "" expr_type
                                      then Hashtbl.add type_tbl v (Hashtbl.find conjecture.atom_type_table v)
                                      else 
                                      Hashtbl.add type_tbl v (TypeUtils.get_return_type "" (Sexp.of_string expr_type))
               ) vars; type_tbl

let synthesize p_ctxt conjecture =
  Printf.printf "Synthesizing for conjecture %s\n" conjecture.conjecture_str;
  let examples = Examples.get_examples (p_ctxt.dir ^ "/examples.txt")
  in
  let lfind_var_outputs = evaluate_generalized_expr conjecture examples p_ctxt
  in let synth_terms = get_terms_to_synthesize [] conjecture.body_sexp conjecture.lfind_vars conjecture.all_expr_type_table
  (* the following part will be a iter over all synth terms for now I am taking the head element *)
  in let sorted_synth_terms = LatticeUtils.sort_by_size synth_terms
  in let curr_synth_term = List.hd (sorted_synth_terms)
  in Printf.printf "Synth term is %s\n" (Sexp.string_of_sexpr curr_synth_term);
  let output_examples = (Evaluate.evaluate_coq_expr curr_synth_term examples p_ctxt)
  in let vars_for_synthesis = (get_variables_except_expr conjecture.body_sexp curr_synth_term [] p_ctxt.vars conjecture.lfind_vars)
  in let var_types = get_type_vars conjecture vars_for_synthesis
  in let output_type = (Hashtbl.find conjecture.all_expr_type_table (Sexp.string_of_sexpr curr_synth_term))
  in Hashtbl.add var_types "output" ( TypeUtils.get_return_type "" (Sexp.of_string output_type));
  Hashtbl.iter (fun k v -> Printf.printf "%s -> %s\n" k v) var_types;
  (* construct the string of examples to dump to synthesis file *)
  let myth_examples = Examples.gen_synthesis_examples examples lfind_var_outputs output_examples vars_for_synthesis
  in let vars_for_synthesis = List.append vars_for_synthesis ["output"]
  in Myth.enumerate_expressions p_ctxt conjecture.conjecture_name myth_examples var_types vars_for_synthesis