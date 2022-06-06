open Sexp
open Utils
open LatticeUtils
open ProofContext
open ExprUtils


let add_expr_vars expr_vars vars var sigma =
  let is_exists_in_vars = List.exists (fun v -> String.equal v var) vars
  in let is_exists_in_sigma = try 
                                let _ = Hashtbl.find sigma var
                                in true
                              with _ -> false
  in let is_dup = List.exists (fun v -> String.equal v var) expr_vars
  in if (is_exists_in_vars || is_exists_in_sigma) & (not is_dup) 
     then List.append expr_vars [var]
     else expr_vars

let rec get_variables_in_expr expr expr_vars vars sigma : string list=
  match expr with
  | (Atom v) :: tl -> 
                      get_variables_in_expr tl (add_expr_vars expr_vars vars v sigma) vars sigma
  | (Expr hd) :: tl ->
                      let head_vars = get_variables_in_expr hd expr_vars vars sigma
                        in get_variables_in_expr tl head_vars vars sigma
  | [] -> expr_vars

let gen_var next_val = 
  "lf" ^ (string_of_int (next_val()))

let generalize_expr_with_var (expr: Sexp.t list) (var_name: string) (s: Sexp.t list)=
  let rec aux (acc: string list) = function 
  | (Atom tag)::tl -> 
                      if (equal [Atom tag] (expr)) then
                        (aux ((var_name)::acc) tl)
                      else
                        (aux ((protect tag)::acc) tl)
  | (Expr e)::tl ->
    let str_to_concat= (aux [] e)
    in
    let to_app = if (equal e expr) then 
                  var_name
                 else 
                  "(" ^ (String.concat " " str_to_concat) ^ ")"
      in
      aux (to_app::acc) tl
  | [] -> (List.rev acc)
  in
  let str_expr = (aux [] s)
  in String.concat " " str_expr
  
let generalize_expr (s: Sexp.t list) (expr: Sexp.t list) (next_val: unit -> int) =
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
    in
    let to_app = if (equal e expr) then
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
  
let generalize_exprL (exprL: Sexp.t list list)
                     (type_table: (string, string) Hashtbl.t)
                     (goal: Sexp.t list)
                     (hypotheses: Sexp.t list list)
                     =
  let sigma = Hashtbl.create 100
  in let counter = ref 0
  in List.fold_left
             (fun (acc, sigma, vars, acc_hyps) e ->
                let gen, var_name = (generalize_expr acc e (Utils.next_val counter))
                in if String.equal var_name ""
                    then 
                      acc, sigma, vars, acc_hyps
                    else 
                    (
                      let subs_hyps = List.map (fun hyp -> of_string (generalize_expr_with_var e var_name hyp)) acc_hyps
                      in (Hashtbl.add sigma var_name (e, (Hashtbl.find type_table (string_of_sexpr e))));
                        of_string gen, sigma, var_name::vars, subs_hyps
                    )
             )
             (goal, sigma, [], hypotheses) exprL

let get_var_type t =
  let return_type = try (TypeUtils.get_return_type "" (of_string t)) with _ -> t
  in return_type

let get_conjecture (gen: string) sigma var_str counter: string =
  let conjecture_str = ": forall " ^ var_str
  in
  conjecture_str ^ " , " ^ gen

let get_all_conjectures generalizations
                        (atom_type_table : (string, string) Hashtbl.t)
                        (expr_type_table : (string, string) Hashtbl.t)
                        (p_ctxt : proof_context)
                        : conjecture list =
  (* 
    Input: Set of generalizations, type tables and proof context
    Output: De-duped set of generalizations as conjecture objects
  *)
  let counter = ref 0
  in let generalized_conjecture_strings =
              List.map (fun (g, sigma, vars, hyps) ->
                  let gvars = (get_variables_in_expr g [] p_ctxt.vars sigma)
                  in let var_types = Hashtbl.create (List.length gvars)
                  in let var_str = (List.fold_left (fun acc v -> 
                                          acc ^ 
                                          (
                                            try 
                                              Hashtbl.add var_types v (Hashtbl.find atom_type_table v);
                                              " (" 
                                              ^ v 
                                              ^":"
                                              ^ (Hashtbl.find atom_type_table v) 
                                              ^ ")"
                                            with _ -> 
                                            (
                                              let _, t = Hashtbl.find sigma v
                                              in let return_type = (get_var_type t)
                                              in Hashtbl.add var_types v return_type;
                                              let v_type = if String.equal return_type ""
                                              then return_type
                                              else ":" ^ return_type
                                              in
                                              "("^ v ^ v_type ^")"
                                            )
                                          )
                                          ) "" gvars)
                  in
                  let var_str, _, normalized_vars = Sexp.normalize_sexp g var_types
                  in let normalized_g = Sexp.normalize_sexp_vars g normalized_vars
                  in let conjecture_body = (get_conjecture normalized_g sigma var_str counter)
                  in
                   {
                      sigma=sigma; 
                      conjecture_str="";
                      conjecture_name="";
                      body=conjecture_body;
                      body_sexp=(Sexp.of_string normalized_g);
                      lfind_vars=vars;
                      all_expr_type_table = expr_type_table;
                      atom_type_table = atom_type_table;
                      hyps = hyps;
                      cgs = [];
                      vars = gvars;
                      vars_with_types = var_str;
                      normalized_var_map = normalized_vars;
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
                                       hyps = c.hyps;
                                       cgs = c.cgs;
                                       vars = c.vars;
                                       vars_with_types = c.vars_with_types;
                                       normalized_var_map = c.normalized_var_map;
                                      }
                        in (conj::acc)
                    ) [] conjectures
         
let construct_all_generalizations (generalization_set: Sexp.t list list list) 
                                  (type_table: (string, string) Hashtbl.t)
                                  (goal: Sexp.t list)
                                  (hypotheses: Sexp.t list list)
                                   =
  (* 
    Input: Powerset of all terms, types, and goal
    Output: Tuple<generalized goal, generalization sigma, generalization variables> list
  *)
  List.map
        (
          fun g -> let sorted_g = LatticeUtils.sort_by_size g
          in generalize_exprL sorted_g type_table goal hypotheses
        ) generalization_set

