
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
}

let remove_conjecture_dups conjectures = 
    List.fold_left (fun acc s -> let is_present = List.exists (fun a -> String.equal s.body a.body) acc
                                 in if is_present then acc else List.append acc [s]
                   ) [] conjectures

let sort_by_size (terml : Sexp.t list list) = 
    List.sort (fun a b -> (Sexp.size b) - (Sexp.size a)) terml

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

let rec sets = function
  | []    -> [[]]
  | x::xs -> let ls = sets xs in
               List.map (fun l -> x::l) ls @ ls

let conjs_to_string conjectures =
    List.fold_left (fun acc conj -> acc ^ conj.conjecture_str ^ "\n") "" conjectures

let construct_implications conc hyps =
    List.fold_left (fun acc hyp -> "(" ^ hyp ^  "->" ^ acc ^ ")") conc hyps

let contains s1 s2 =
    let re = Str.regexp_string s2 in
    try 
        ignore (Str.search_forward re s1 0); 
        true
    with Not_found -> false
    
let get_dir paths =
  List.fold_left (fun acc path -> let path_str = (Utils.get_str_of_pp (Loadpath.pp (path)))
                                  in let is_contains = contains path_str "coq"
                                  in if is_contains || not (String.equal acc "") then acc else List.hd (List.rev (String.split_on_char ' ' path_str))
                 ) "" paths
  