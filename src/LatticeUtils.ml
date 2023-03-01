
open Sexp
open ProofContext
open String
open Utils


exception Failure of string

type goal = {
    hypos : string list;
    conc : string ;
}

type conjecture = {
  sigma : (string, Sexp.t list * string) Hashtbl.t;
  conjecture_str : string;
  body : string;
  conjecture_name:string;
  body_sexp : Sexp.t list;
  lfind_vars : string list;
  all_expr_type_table : (string, string) Hashtbl.t;
  atom_type_table : (string, string) Hashtbl.t;
  hyps : Sexp.t list list;
  cgs : string list;
  vars: string list;
  vars_with_types: string;
  normalized_var_map: (string, string) Hashtbl.t;
}

let remove_conjecture_dups conjectures = 
    List.fold_left (fun acc s -> let is_present = List.exists (fun a -> String.equal s.body a.body) acc
                                 in if is_present then acc else List.append acc [s]
                   ) [] conjectures

let sort_by_size (terml : Sexp.t list list) :Sexp.t list list =
    (* 
        Input: List of terms
        Output: Sorted list of terms in descending order
    *)
    List.sort (fun a b -> (Sexp.size b) - (Sexp.size a)) terml

let update_type_table (atoms : string list) c_ctx type_tbl = 
    List.iter (fun a -> 
                    (* We may want to skip atoms that do not have a proper type *)
                    try 
                    (let typ = TypeUtils.get_type_of_atom c_ctx.env c_ctx.sigma a
                    in Hashtbl.replace type_tbl (a) typ)
                    with _ -> ();
              ) atoms; type_tbl

let add_variable (variables: string list ) (var: string): string list = 
    let var_exists = List.exists (fun curr_var -> String.equal curr_var var) variables
    in if var_exists then variables
        else (var :: variables)

let rec index_of (x: Sexp.t list) (lst: Sexp.t list list) =
    match lst with
    | [] -> raise (Failure "Not Found")
    | h :: t -> if Sexp.equal x h then 0 else 1 + index_of x t

let rec sets = function
  | []    -> [[]]
  | x::xs -> let ls = sets xs in
               List.map (fun l -> x::l) ls @ ls

let conjs_to_string (conjectures: conjecture list) : string =
    List.fold_left (fun acc conj -> acc ^ conj.conjecture_str ^ "\n") "" conjectures

let construct_implications (conc: string) (hyps: Sexp.t list list) : string =
    List.fold_left (fun acc hyp -> "(" ^ (Sexp.string_of_sexpr hyp) ^  "->" ^ acc ^ ")") conc hyps

let gen_conjecture_name prefix inc = 
    prefix ^ "conj" ^ (string_of_int (inc()))
                   