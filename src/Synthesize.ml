open LatticeUtils
open ProofContext
open Stats
open Consts


let term_contains_gen_var term gen_vars =
  List.exists (fun gvar -> 
                   Utils.contains (Sexp.string_of_sexpr term) gvar
              ) gen_vars

let add_synthesis_term acc gen_vars term type_tbl topconj =
  let term_type = try (Hashtbl.find type_tbl (Sexp.string_of_sexpr term)) with _ -> ""
  in let return_type = try TypeUtils.get_return_type "" (Sexp.of_string term_type) with _ -> term_type
  in 
  (* TODO: Need to ensure @eq is not added when considering variables to generalize. One way would eb check Type in return type instead of equal.*)
  if String.equal return_type type_decl
    then acc, false
    else 
        (
          let exists = List.exists (fun e -> Sexp.equal e term) acc
          in if exists 
             then acc, false
             else 
                  (* if term_contains_gen_var term gen_vars
                  then acc, false
                  else *)
                  (
                  if Sexp.equal [Expr term] topconj
                  then acc, false
                  else term :: acc, true
                  )
        )

(* 
   We pick terms based on the size. 
   Add the largest expression that can be replaced for synthesis. 
*)
let rec get_terms_to_synthesize (acc : Sexp.t list list) (conjecture: Sexp.t list)
                                (gen_vars: string list) type_tbl topconj add_atoms
                                : Sexp.t list list =
  match conjecture with
  | (Atom a) :: tl -> if add_atoms then
                      (
                        let new_acc, is_added = (add_synthesis_term acc gen_vars [Atom a] type_tbl topconj)
                        in get_terms_to_synthesize new_acc tl gen_vars type_tbl topconj add_atoms
                      ) 
                      else
                        get_terms_to_synthesize acc tl gen_vars type_tbl topconj add_atoms
  | (Expr head) :: tl -> 
                         (
                          let new_acc, is_added = (add_synthesis_term acc gen_vars head type_tbl topconj)
                          in if is_added then
                          get_terms_to_synthesize new_acc tl gen_vars type_tbl topconj add_atoms
                          else 
                          (
                            let head_terms = get_terms_to_synthesize new_acc head gen_vars type_tbl topconj add_atoms
                            in get_terms_to_synthesize head_terms tl gen_vars type_tbl topconj add_atoms
                          )
                         )
  | [] -> acc

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

let get_quantified_var var_types =
  Hashtbl.fold (fun k v acc -> if String.equal k synthesis_op
                               then acc
                               else acc ^ " " ^ "(" ^ k ^ " : " ^ v ^ ")"
               ) var_types ""

let get_synthesis_conjecture curr_synth_term conjecture var_types counter synthesized_expr =
  Log.debug (Consts.fmt "synth term is %s" (Sexp.string_of_sexpr curr_synth_term));
  Log.debug (Consts.fmt "synthesized expression is %s" synthesized_expr);
  let synthesized_expr = "(" ^ synthesized_expr ^ ")"
  in let replaced_conj = Sexp.replace_sub_sexp conjecture.body_sexp curr_synth_term synthesized_expr
  in Log.debug (Consts.fmt "replaced conjcture is %s" replaced_conj);
  (* in  *)
  let conj_prefix = conjecture.conjecture_name ^ "synth"
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

let filter_valid_conjectures synthesized_conjectures p_ctxt original_conjecture cached_lemmas =
  List.fold_right (fun (s, conj) acc ->
                      (
                        let cached_output = try
                                            Some (Hashtbl.find cached_lemmas conj.body)
                                            with _ -> None
                        in match cached_output with
                        | None -> (
                                    let is_valid = Valid.check_validity conj p_ctxt
                                    in Hashtbl.add cached_lemmas conj.body is_valid;
                                    if is_valid
                                        then (s,conj)::acc
                                        else acc
                                  )
                        | Some (validity) -> Log.debug ("Here in cached validity check, so we do not send this back as new computation");
                                        acc
                        
                      )
                  ) synthesized_conjectures []


let filter_provable_conjectures valid_conjectures p_ctxt original_conjecture =
  List.filter (fun (_, conj) -> (Provable.check_lfind_theorem_add_axiom p_ctxt conj.conjecture_name conj.conjecture_str)) valid_conjectures

let synthesize_lemmas conjecture ml_examples coq_examples p_ctxt cached_lemmas curr_synth_term =
  Log.debug (Consts.fmt "Synth term is %s\n" (Sexp.string_of_sexpr curr_synth_term));
  let all_vars = List.append p_ctxt.vars conjecture.lfind_vars
  in let _, output_examples = (Evaluate.evaluate_coq_expr curr_synth_term coq_examples p_ctxt all_vars conjecture.sigma (Some conjecture))
  
  in let vars_for_synthesis = (get_variables_except_expr conjecture.body_sexp curr_synth_term [] p_ctxt.vars conjecture.lfind_vars)
  in let vars_for_synthesis = if Int.equal (List.length vars_for_synthesis) 0 then
                                (* the case when we make the entire conjecture a hole *)
                                ExprUtils.get_variables_in_expr conjecture.body_sexp [] all_vars
                              else vars_for_synthesis
  in let var_types = ExprUtils.get_type_vars conjecture vars_for_synthesis
  in Hashtbl.iter (fun k _ ->( print_endline k;())) conjecture.sigma;
  let subst_synthesis_term = ExprUtils.subst_lfind_vars_in_expr curr_synth_term conjecture.sigma
  in 
  (* Sometimes the subst_synthesis_term can have () or not around the expression, so when lookup fails we are going to take the expr within () TODO: This is a hack, need to check why all_expr_type_table table didnt include ()*)
  let output_type = try (Hashtbl.find conjecture.all_expr_type_table subst_synthesis_term)  
  with _ -> (Hashtbl.find conjecture.all_expr_type_table (String.sub subst_synthesis_term 1 ((String.length subst_synthesis_term) -2)))  
  in 
  Hashtbl.add var_types synthesis_op ( try TypeUtils.get_return_type "" (Sexp.of_string output_type) with _ -> output_type);
  let myth_examples = Examples.gen_synthesis_examples ml_examples output_examples vars_for_synthesis conjecture.sigma
  in LogUtils.write_list_to_log myth_examples "myth examples";
  let vars_for_synthesis = List.append vars_for_synthesis [synthesis_op]
  in let enumerated_exprs = Myth.enumerate_expressions p_ctxt conjecture.conjecture_name myth_examples var_types vars_for_synthesis true
  in let counter = ref 0
  in let synthesized_conjectures = List.map (get_synthesis_conjecture curr_synth_term conjecture var_types (Utils.next_val counter)) enumerated_exprs
  in let valid_conjectures = filter_valid_conjectures synthesized_conjectures p_ctxt conjecture !cached_lemmas
  in let provable_conjectures = filter_provable_conjectures valid_conjectures p_ctxt conjecture
  in let synth_stat = {
                        synthesis_term = (Sexp.string_of_sexpr curr_synth_term);
                        enumerated_exprs = enumerated_exprs;
                        valid_lemmas = valid_conjectures;
                        provable_lemmas = provable_conjectures;
                      }
  in synth_stat

let synthesize cached_lemmas p_ctxt ml_examples coq_examples conjecture=
  Log.debug(Consts.fmt "Synthesizing for conjecture %s\n" conjecture.conjecture_str);
  Log.debug(Consts.fmt "#Coq Input Examples %d\n" (List.length coq_examples));
  Log.debug(Consts.fmt "#ML Input Examples %d\n" (List.length ml_examples));
  (
    let first_synth_terms = get_terms_to_synthesize [] conjecture.body_sexp conjecture.lfind_vars conjecture.all_expr_type_table conjecture.body_sexp false
    in let synth_terms = if List.length first_synth_terms == 0 
                         then get_terms_to_synthesize [] conjecture.body_sexp conjecture.lfind_vars conjecture.all_expr_type_table conjecture.body_sexp true 
                         else first_synth_terms
    in Log.debug (Consts.fmt "Size of synth terms is %d" (List.length synth_terms));
    List.iter (fun s -> print_endline (Sexp.string_of_sexpr s)) synth_terms;
    let sorted_synth_terms = LatticeUtils.sort_by_size synth_terms
    in let synth_stats = List.map (synthesize_lemmas conjecture ml_examples coq_examples p_ctxt cached_lemmas) sorted_synth_terms
    in let gen_stat = {
                        conjecture = conjecture;
                        is_valid = false;
                        is_provable = false;
                        synthesis_stats = synth_stats;
                      }
    in Log.write_to_log (genstat_to_string gen_stat) !Log.stats_log_file;
    global_stat := gen_stat :: !global_stat;
    ()
  )

  