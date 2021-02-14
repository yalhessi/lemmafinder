
open Sexp
open ProofContext
open String
open Utils


exception Failure of string

type goal = {
    hypos : string list;
    conc : string ;
}   

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