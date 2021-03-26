open LatticeUtils
open ProofContext
open Stats
open Consts

let term_contains_gen_var term gen_vars =
  List.exists (fun gvar -> 
                   Utils.contains (Sexp.string_of_sexpr term) gvar
              ) gen_vars

let add_synthesis_term acc gen_vars term type_tbl =
  let term_type = try (Hashtbl.find type_tbl (Sexp.string_of_sexpr term)) with _ -> ""
  in let return_type = TypeUtils.get_return_type "" (Sexp.of_string term_type)
  in if String.equal return_type type_decl
    then acc, false
    else 
        (
          let exists = List.exists (fun e -> Sexp.equal e term) acc
          in if exists 
             then acc, false
             else if term_contains_gen_var term gen_vars
                  then acc, false
                  else term :: acc, true
        )

(* 
   We pick terms based on the size. 
   Add the largest expression that can be replaced for synthesis. 
*)
let rec get_terms_to_synthesize (acc : Sexp.t list list) (conjecture: Sexp.t list)
                                (gen_vars: string list) type_tbl : Sexp.t list list =
  match conjecture with
  | (Atom a) :: tl -> get_terms_to_synthesize acc tl gen_vars type_tbl
  | (Expr head) :: tl -> let new_acc, is_added = (add_synthesis_term acc gen_vars head type_tbl)
                         in if is_added then
                         get_terms_to_synthesize new_acc tl gen_vars type_tbl
                         else 
                         (
                          let head_terms = get_terms_to_synthesize new_acc head gen_vars type_tbl
                          in get_terms_to_synthesize head_terms tl gen_vars type_tbl
                         )
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

let get_quantified_var var_types =
  Hashtbl.fold (fun k v acc -> if String.equal k synthesis_op
                               then acc
                               else acc ^ " " ^ "(" ^ k ^ " : " ^ v ^ ")"
               ) var_types ""

let get_synthesis_conjecture curr_synth_term conjecture var_types counter synthesized_expr  =
  let synthesized_expr = "(" ^ synthesized_expr ^ ")"
  in let replaced_conj = Sexp.replace_sub_sexp conjecture.body_sexp curr_synth_term synthesized_expr
  in let conj_prefix = conjecture.conjecture_name ^ "synth"
  in let synth_conj_name = LatticeUtils.gen_conjecture_name conj_prefix counter
  in let synth_conj = synth_conj_name ^ " " ^ ": forall " ^ (get_quantified_var var_types) ^ ", " ^ replaced_conj
  in let synthesis_conjecture = {
                                  sigma = Hashtbl.create 0;
                                  conjecture_str = synth_conj;
                                  body = replaced_conj;
                                  conjecture_name = synth_conj_name;
                                  body_sexp = [];
                                  lfind_vars = [];
                                  all_expr_type_table = Hashtbl.create 0;
                                  atom_type_table = var_types
                                }
  in synthesized_expr, synthesis_conjecture

let filter_valid_conjectures synthesized_conjectures p_ctxt original_conjecture =
  List.filter (fun (_, conj) -> (Valid.check_validity conj p_ctxt)) synthesized_conjectures

let filter_provable_conjectures valid_conjectures p_ctxt original_conjecture =
  List.filter (fun (_, conj) -> (Provable.check_lfind_theorem_add_axiom p_ctxt conj.conjecture_str)) valid_conjectures

let synthesize_lemmas curr_synth_term conjecture examples p_ctxt generalized_var_output =
  Log.debug (Consts.fmt "Synth term is %s\n" (Sexp.string_of_sexpr curr_synth_term));
  let output_examples = (Evaluate.evaluate_coq_expr curr_synth_term examples p_ctxt)
  in let vars_for_synthesis = (get_variables_except_expr conjecture.body_sexp curr_synth_term [] p_ctxt.vars conjecture.lfind_vars)
  in let var_types = get_type_vars conjecture vars_for_synthesis
  in let output_type = (Hashtbl.find conjecture.all_expr_type_table (Sexp.string_of_sexpr curr_synth_term))
  in Hashtbl.add var_types synthesis_op ( TypeUtils.get_return_type "" (Sexp.of_string output_type));
  let myth_examples = Examples.gen_synthesis_examples examples generalized_var_output output_examples vars_for_synthesis
  in let vars_for_synthesis = List.append vars_for_synthesis [synthesis_op]
  in let enumerated_exprs = Myth.enumerate_expressions p_ctxt conjecture.conjecture_name myth_examples var_types vars_for_synthesis true
  in let counter = ref 0
  in let synthesized_conjectures = List.map (get_synthesis_conjecture curr_synth_term conjecture var_types (Utils.next_val counter)) enumerated_exprs
  in let valid_conjectures = filter_valid_conjectures synthesized_conjectures p_ctxt conjecture
  in let provable_conjectures = filter_provable_conjectures valid_conjectures p_ctxt conjecture
  in let synth_stat = {
                        synthesis_term = (Sexp.string_of_sexpr curr_synth_term);
                        enumerated_exprs = enumerated_exprs;
                        valid_lemmas = valid_conjectures;
                        provable_lemmas = provable_conjectures;
                      }
  in synth_stat

let synthesize p_ctxt conjecture =
  Log.debug(Consts.fmt "Synthesizing for conjecture %s\n" conjecture.conjecture_str);
  let example_file = Consts.fmt "%s/examples_%s.txt" p_ctxt.dir p_ctxt.fname
  in let examples = Examples.get_examples example_file
  in
  let generalized_var_output = evaluate_generalized_expr conjecture examples p_ctxt
  in let synth_terms = get_terms_to_synthesize [] conjecture.body_sexp conjecture.lfind_vars conjecture.all_expr_type_table
  (* the following part will be a iter over all synth terms for now I am taking the head element *)
  in let sorted_synth_terms = LatticeUtils.sort_by_size synth_terms
  in let synth_stats = List.map (fun synth_term -> (synthesize_lemmas synth_term conjecture examples p_ctxt generalized_var_output)) sorted_synth_terms
  in let gen_stat = {
                      conjecture = conjecture;
                      is_valid = false;
                      is_provable = false;
                      synthesis_stats = synth_stats;
                    }
  in Log.write_to_log (genstat_to_string gen_stat) !Log.stats_log_file;
  global_stat := gen_stat :: !global_stat;
  ()
  