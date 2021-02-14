open Utils
open ProofContext
open LatticeUtils
open Sexp

let rec collect_terms_w_position (acc: (Sexp.t list * int) list) (atoms : string list) (sexp: Sexp.t list) : ((Sexp.t list * int) list) * string list =
  match sexp with
  | (Atom a) :: tl -> collect_terms_w_position acc (a :: atoms) tl
  | (Expr head) :: tl -> let new_acc, _ = (add_term acc head)
                          in let head_terms, head_atoms = collect_terms_w_position new_acc atoms head
                          in collect_terms_w_position head_terms head_atoms tl
  | [] -> acc, atoms

let get_type_table (terms: (Sexp.t list * int) list) c_ctx =  
  let type_tbl = Hashtbl.create (List.length terms)
  in List.iter (fun (term, count) -> let typ = Utils.get_type_of_exp c_ctx.env c_ctx.sigma (Utils.str_to_constr (string_of_sexpr term))
                            in let typ_str = Utils.get_str_of_pp (Printer.pr_econstr_env c_ctx.env c_ctx.sigma typ)
                            in Hashtbl.replace type_tbl (string_of_sexpr term) typ_str
                ) 
                terms; type_tbl

let powerset_to_string (p_set: (Sexp.t list * int) list list) = 
  List.fold_left (fun (acc: string) (elem: (Sexp.t list * int) list) 
                      -> let elem_str = "[" ^ (List.fold_left (fun accl (e, count) -> (string_of_sexpr e) ^ ":" ^ (string_of_int count) ^ ";" ^ accl) "" elem) ^ "]"
                          in acc ^ "\n" ^ elem_str
                  ) "" p_set

let abstract (p_ctxt : proof_context) (c_ctxt : coq_context) =
  let recursive_funcs = p_ctxt.functions
  in let hypo_sexps = List.map (fun hyp -> Sexp.of_string hyp) p_ctxt.hypotheses
  in let conc_sexp = Sexp.of_string p_ctxt.goal    
  (* in let hypo_terms = List.fold_left (fun acc hypo_sexp -> List.append (collect_terms [] hypo_sexp) acc) [] hypo_sexps *)
  in let hypo_terms = []
  in let conc_terms, atoms = (collect_terms_w_position [] [] conc_sexp) 
  (* in List.iter (fun (e, count) -> print_endline ((string_of_sexpr e) ^ ":" ^ (string_of_int count))) conc_terms; *)
  in let all_terms = List.tl (List.append conc_terms hypo_terms)
  in let expr_type_table = get_type_table (List.append conc_terms hypo_terms) c_ctxt
  in let atom_type_table = (update_type_table atoms c_ctxt (Hashtbl.create 100))
  (* in Hashtbl.iter (fun x y -> Printf.printf "%s -> %s\n" x y) atom_type_table; *)
  (* in Printf.printf "Length of list of terms %s \n" (string_of_int (List.length all_terms)); *)
  in let generalization_set = sets all_terms
  in Printf.printf "Generalization power set \n [ %s ]\n\n" (powerset_to_string generalization_set);
  Printf.printf "Generalizations \n";
  let generalizations = Generalize_WPositions.construct_all_generalizations generalization_set expr_type_table conc_sexp
  in (Generalize_WPositions.print_generalizations generalizations atom_type_table);