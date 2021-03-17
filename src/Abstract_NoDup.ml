open Utils
open ProofContext
open LatticeUtils
open Sexp

let rec collect_terms_no_dup (acc: (Sexp.t list) list) (atoms : string list) (sexp: Sexp.t list) : ((Sexp.t list) list) * string list =
  match sexp with
  | (Atom a) :: tl -> collect_terms_no_dup acc (a :: atoms) tl
  | (Expr head) :: tl -> let new_acc = (add_term_remove_dup acc head)
                          in let head_terms, head_atoms = collect_terms_no_dup new_acc atoms head
                          in collect_terms_no_dup head_terms head_atoms tl
  | [] -> acc, atoms

let get_type_table (terms: (Sexp.t list) list) c_ctx =  
  let type_tbl = Hashtbl.create (List.length terms)
  in List.iter (fun term -> let typ = TypeUtils.get_type_of_exp c_ctx.env c_ctx.sigma term
                            in Hashtbl.replace type_tbl (string_of_sexpr term) typ
               )
               terms; type_tbl

let powerset_to_string (p_set: (Sexp.t list) list list) = 
  List.fold_left (fun (acc: string) (elem: (Sexp.t list) list) 
                      -> let elem_str = "[" ^ (List.fold_left (fun accl e -> (string_of_sexpr e) ^ ";" ^ accl) "" elem) ^ "]"
                          in acc ^ "\n" ^ elem_str
                  ) "" p_set

let get_generalizable_terms all_terms expr_type_table =
  List.fold_left (fun acc term -> let term_type = Hashtbl.find expr_type_table (string_of_sexpr term)
                                  in let return_type = TypeUtils.get_return_type "" (of_string term_type)
                                  in if String.equal return_type "Type"
                                     then acc
                                     else (add_term_remove_dup acc term)
                 ) [] all_terms

let abstract (p_ctxt : proof_context) (c_ctxt : coq_context) =
  let with_hyp = false
  in let recursive_funcs = p_ctxt.functions
  in let hypo_sexps = List.map (fun hyp -> Sexp.of_string hyp) p_ctxt.hypotheses
  in let conc_sexp = Sexp.of_string p_ctxt.goal
  in let conc_terms, conc_atoms = (collect_terms_no_dup [] [] conc_sexp)
  in let hypo_terms, hyp_atoms = List.fold_left (fun (hyp_terms,hyp_atoms) hypo_sexp -> 
                                                                let terms,atoms = (collect_terms_no_dup [] [] hypo_sexp)
                                                                in List.append hyp_terms terms, List.append atoms hyp_atoms
                                           ) ([],[]) hypo_sexps
  in let atoms = if with_hyp
                        then List.append conc_atoms hyp_atoms
                        else conc_atoms
  in let expr_type_table = get_type_table (List.append conc_terms hypo_terms) c_ctxt
  in let atom_type_table = (update_type_table atoms c_ctxt (Hashtbl.create 100))
  (* in Hashtbl.iter (fun x y -> Printf.printf "%s -> %s\n" x y) atom_type_table;
  Hashtbl.iter (fun x y -> Printf.printf "%s -> %s\n" x y) expr_type_table; *)
  
  in let all_terms = if with_hyp 
                        then List.tl (List.append conc_terms (List.tl hypo_terms)) 
                        else List.tl (conc_terms)
  in let terms = get_generalizable_terms all_terms expr_type_table
  in Printf.printf "Size of terms list %d\n and Terms from the goal [%s]\n" (List.length terms) (List.fold_left (fun acc e -> acc ^ ";" ^ ((string_of_sexpr e))) "" terms);
  (* in Printf.printf "Length of list of terms %s \n" (string_of_int (List.length all_terms)); *)
  let generalization_set = sets terms
  (* in Printf.printf "Generalization power set \n [ %s ]\n\n" (powerset_to_string generalization_set); *)
  (* in Printf.printf "Generalizations \n"; *)
  in let hypo_implies_conc =
    if with_hyp then LatticeUtils.construct_implications p_ctxt.goal p_ctxt.hypotheses
    else (string_of_sexpr conc_sexp)
  (* in print_endline hypo_implies_conc; *)
  in let generalizations = Generalize_NoDup.construct_all_generalizations generalization_set expr_type_table (of_string hypo_implies_conc)
  in let conjectures = (Generalize_NoDup.get_all_conjectures generalizations atom_type_table expr_type_table p_ctxt)
  (* in List.iter (fun c -> Printf.printf "%s\n" (c.conjecture_str)) conjectures; *)
  in conjectures
