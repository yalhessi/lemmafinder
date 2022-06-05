open LatticeUtils
open Sexp
open ProofContext

let vars_is_subset hyp_vars g_vars : bool =
  List.fold_left (fun acc h_var -> 
                      acc && List.exists (fun v -> String.equal v h_var) g_vars
                 ) true hyp_vars

let subst_expr_with_value var_values hyp=
let rec aux (acc: string list) = function 
| (Atom tag)::tl -> (
                      try (aux (("(" ^ (Hashtbl.find var_values tag) ^ ")")::acc) tl)
                        with _ -> (aux ((protect tag)::acc) tl)
                    )
| (Expr e)::tl ->
  let str_to_concat= (aux [] e)
  in
  let to_app = "(" ^ (String.concat " " str_to_concat) ^ ")"
    in
    aux (to_app::acc) tl
| [] -> (List.rev acc)
in
let str_expr = (aux [] hyp)
in String.concat " " str_expr


let get_invalid_hyps (p_ctxt: proof_context) 
                     (c: conjecture) 
                     (cgs_table: (string, string) Hashtbl.t):
                     t list list * t list list=
    List.fold_left 
      (fun (acc_cg, acc) h -> 
        let h_vars = (Generalize_NoDup.get_variables_in_expr h [] p_ctxt.vars c.sigma)
        in
        let is_subset = vars_is_subset h_vars c.vars
        in
        if is_subset then
        (* subst with cgs to evaluate with quickchick *)
          (
            let var_values = Hashtbl.create (List.length h_vars)
            in List.iter (fun h_var -> Hashtbl.add var_values h_var (Hashtbl.find cgs_table h_var)) h_vars;
            let subst_hyp = subst_expr_with_value var_values h
            in
            let s_hyp_c = {
                              sigma=Hashtbl.create 0; 
                              conjecture_str= "lfind_hyp_test : " ^ subst_hyp;
                              conjecture_name="lfind_hyp_test";
                              body="";
                              body_sexp=[];
                              lfind_vars=[];
                              all_expr_type_table = Hashtbl.create 0; 
                              atom_type_table = Hashtbl.create 0; 
                              hyps = [];
                              cgs = [];
                              vars = [];
                              vars_with_types = "";
                              normalized_var_map = Hashtbl.create 0;
                           }
            in let is_valid, _ = Valid.check_validity s_hyp_c p_ctxt
            in if is_valid then acc_cg, h::acc else h::acc_cg, acc
          )
        else
          acc_cg, h::acc
      ) ([],[]) c.hyps

let construct_hyp_goal_conj invalid_hyps c =
  let hyp_goal = List.fold_left (fun acc h -> (Sexp.normalize_sexp_vars h c.normalized_var_map) ^ " -> " ^ acc) "" invalid_hyps
  in let hyp_goal = "forall " ^ c.vars_with_types ^ ", " ^ hyp_goal ^ " " ^ (Sexp.string_of_sexpr c.body_sexp)
  in
  let hyp_conj = {c with
                      conjecture_str= c.conjecture_name ^"_hyp: " ^ hyp_goal;
                      conjecture_name = c.conjecture_name ^"_hyp";
                      body=hyp_goal;
                      body_sexp= Sexp.of_string ("(" ^ hyp_goal ^ " " ^ (Sexp.string_of_sexpr c.body_sexp) ^ ")");
                    }
  in hyp_conj
  

let conjectures_with_hyp (invalid_conjectures: conjecture list) 
                         (p_ctxt: proof_context) =
  List.fold_left 
          (
            fun acc (c: conjecture) ->
            match List.length c.cgs with
            | 0 -> acc
            | _ -> begin
                      let cgs_table = Hashtbl.create (List.length c.vars)
                      in List.iteri (fun index c_var -> Hashtbl.add cgs_table c_var (List.nth c.cgs index)) c.vars;
                      let invalid_hyps, other_hyps = get_invalid_hyps p_ctxt c cgs_table
                      in if (List.length invalid_hyps) > 0 then
                          (
                            let hyp_conj = construct_hyp_goal_conj invalid_hyps c
                            in
                            hyp_conj::acc
                          )
                        else
                          acc
                    end
          ) [] invalid_conjectures