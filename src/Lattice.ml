
open Sexp
open ProofContext
open String
open Utils


exception Failure of string

type goal = {
    hypos : string list;
    conc : string ;
}   

let get_type_table (terms: (Sexp.t list * int) list) c_ctx =  
    let type_tbl = Hashtbl.create (List.length terms)
    in List.iter (fun (term, count) -> let typ = Utils.get_type_of_exp c_ctx.env c_ctx.sigma (Utils.str_to_constr (string_of_sexpr term))
                              in let typ_str = Utils.get_str_of_pp (Printer.pr_econstr_env c_ctx.env c_ctx.sigma typ)
                              in Hashtbl.replace type_tbl (string_of_sexpr term) typ_str
                 ) 
                 terms; type_tbl

let update_type_table (atoms : string list) c_ctx type_tbl = 
    List.iter (fun a -> let typ = Utils.get_type_of_exp c_ctx.env c_ctx.sigma (Utils.str_to_constr a)
                        in let typ_str = Utils.get_str_of_pp (Printer.pr_econstr_env c_ctx.env c_ctx.sigma typ)
                        in Hashtbl.replace type_tbl (a) typ_str
              ) atoms; type_tbl

let add_variable (variables: string list ) (var: string): string list = 
    let var_exists = List.exists (fun curr_var -> String.equal curr_var var) variables
    in if var_exists then variables
        else (var :: variables)

let rec index_of (x: Sexp.t list) (lst: Sexp.t list list) =
    match lst with
    | [] -> raise (Failure "Not Found")
    | h :: t -> if Sexp.equal x h then 0 else 1 + index_of x t

let rec collect_terms (acc: (Sexp.t list * int) list) (atoms : string list) (sexp: Sexp.t list) : ((Sexp.t list * int) list) * string list =
    match sexp with
    | (Atom a) :: tl -> collect_terms acc (a :: atoms) tl
    | (Expr head) :: tl -> let new_acc, _ = (add_term acc head)
                            in let head_terms, head_atoms = collect_terms new_acc atoms head
                            in collect_terms head_terms head_atoms tl
    | [] -> acc, atoms

let powerset_to_string (p_set: (Sexp.t list * int) list list) = 
    List.fold_left (fun (acc: string) (elem: (Sexp.t list * int) list) 
                        -> let elem_str = "[" ^ (List.fold_left (fun accl (e, count) -> (string_of_sexpr e) ^ ":" ^ (string_of_int count) ^ ";" ^ accl) "" elem) ^ "]"
                            in acc ^ "\n" ^ elem_str
                    ) "" p_set

let rec sets = function
  | []    -> [[]]
  | x::xs -> let ls = sets xs in
               List.map (fun l -> x::l) ls @ ls
                 
let abstract (p_ctxt : proof_context) (c_ctxt : coq_context) =
    let recursive_funcs = p_ctxt.functions
    in let hypo_sexps = List.map (fun hyp -> Sexp.of_string hyp) p_ctxt.hypotheses
    in let conc_sexp = Sexp.of_string p_ctxt.goal    
    (* in let hypo_terms = List.fold_left (fun acc hypo_sexp -> List.append (collect_terms [] hypo_sexp) acc) [] hypo_sexps *)
    in let hypo_terms = []
    in let conc_terms, atoms = (collect_terms [] [] conc_sexp) 
    (* in List.iter (fun (e, count) -> print_endline ((string_of_sexpr e) ^ ":" ^ (string_of_int count))) conc_terms; *)
    in let all_terms = List.tl (List.append conc_terms hypo_terms)
    in let expr_type_table = get_type_table (List.append conc_terms hypo_terms) c_ctxt
    in let atom_type_table = (update_type_table atoms c_ctxt (Hashtbl.create 100))
    (* in Hashtbl.iter (fun x y -> Printf.printf "%s -> %s\n" x y) atom_type_table; *)
    (* in Printf.printf "Length of list of terms %s \n" (string_of_int (List.length all_terms)); *)
    in let generalization_set = sets all_terms
    in Printf.printf "Generalization power set \n [ %s ]\n\n" (powerset_to_string generalization_set);
    Printf.printf "Generalizations \n";
    let generalizations = Generalize.construct_all_generalizations generalization_set expr_type_table conc_sexp
    in (Generalize.print_generalizations generalizations atom_type_table);