open Sexp
open Utils
open LatticeUtils
open ProofContext
open ExprUtils

let gen_var next_val = 
  "lf" ^ (string_of_int (next_val()))

let generalize_expr s expr next_val =
  let var_name = ref ""
  in let rec aux (acc: string list) = function 
  | (Atom tag)::tl -> 
                      if (equal [Atom tag] (expr)) then
                      (
                        if String.equal !var_name ""
                        then 
                          var_name := (gen_var next_val);
                        (aux ((!var_name)::acc) tl)
                      )
                     else
                        (aux ((protect tag)::acc) tl)
  | (Expr e)::tl ->
    let str_to_concat= (aux [] e)
    in let to_app = if (equal e expr) then
        (  
          if String.equal !var_name ""
          then 
            var_name := (gen_var next_val);
          !var_name
        )
      else 
        "(" ^
        (String.concat " " str_to_concat)
        ^ ")"
      in
      aux (to_app::acc) tl
  | [] -> (List.rev acc)
  in
  let str_expr = (aux [] s)
  in String.concat " " str_expr, !var_name
  
let generalize_exprL exprL type_table goal =
  let sigma = Hashtbl.create 100
  in let counter = ref 0 
  in List.fold_left 
             (fun (acc, sigma, vars) e ->
                let gen, var_name = (generalize_expr acc e (Utils.next_val counter))
                in if String.equal var_name ""
                    then 
                      acc, sigma, vars
                    else 
                    (
                      (
                        (Hashtbl.add sigma var_name (e, (Hashtbl.find type_table (string_of_sexpr e))));
                        of_string gen, sigma, var_name::vars
                      )
                    )
             )
             (goal, sigma, []) exprL

let get_var_type t =
  let return_type = try (TypeUtils.get_return_type "" (of_string t)) with _ -> t
  in
  if String.equal return_type ""
      then return_type
      else ":" ^ return_type

let get_conjecture gen sigma var_str counter: string =
  let conjecture_str = ": forall " ^ var_str
  in let quantified_var_str = Hashtbl.fold (fun k (e, t) acc 
                                            -> acc ^ "("^ k ^ (get_var_type t) ^")"
                                           )  sigma conjecture_str
  in quantified_var_str ^ " , " ^ gen

let get_all_conjectures generalizations atom_type_table expr_type_table (p_ctxt : proof_context)= 
  let counter = ref 0
  in let generalized_conjecture_strings = List.map (fun (g, sigma, vars) ->
                  let gvars = (get_variables_in_expr g [] p_ctxt.vars)
                  in let var_str = (List.fold_left (fun acc v -> acc ^ (" (" ^ v ^":"^ (Hashtbl.find atom_type_table v) ^ ")")) "" gvars)
                  in
                  let conjecture_body = (get_conjecture (string_of_sexpr g) sigma var_str counter)
                  in
                   {
                      sigma=sigma; 
                      conjecture_str="";
                      conjecture_name="";
                      body=conjecture_body;
                      body_sexp=g;
                      lfind_vars=vars;
                      all_expr_type_table = expr_type_table;
                      atom_type_table = atom_type_table;
                     }
                )
            generalizations
  in Log.debug(Consts.fmt "Size of conjecture before de-duplication %d\n" (List.length generalized_conjecture_strings));
  let conjectures = remove_conjecture_dups generalized_conjecture_strings
  in Log.debug(Consts.fmt "Size of conjecture after de-duplication %d\n" (List.length conjectures));
  List.fold_left (fun acc (c:conjecture) -> 
                        let conjecture_name = (gen_conjecture_name "" (Utils.next_val counter))
                        in let conj = {sigma=c.sigma;
                                       body=c.body;
                                       conjecture_name=conjecture_name;
                                       conjecture_str=(conjecture_name ^ c.body);
                                       body_sexp=c.body_sexp;
                                       lfind_vars=c.lfind_vars;
                                       all_expr_type_table = c.all_expr_type_table;
                                       atom_type_table = c.atom_type_table;
                                      }
                        in (conj::acc)
                    ) [] conjectures
         
let construct_all_generalizations generalization_set type_table goal =
  List.map 
        (
          fun g -> let sorted_g = LatticeUtils.sort_by_size g
          in generalize_exprL sorted_g type_table goal
        ) generalization_set

