open Lfindalgo

let collect_terms_atoms () =
  let state = "(@eq listnat (rev (app x y)) (app (rev y) (rev x)))"
  in let state_sexp = Sexp.of_string state
  in let terms, atoms = Abstract_NoDup.collect_terms_no_dup [] [] state_sexp
  in
  let expected_atoms = ["y"; "x"; "app"; "rev"; "listnat"; "@eq"]
  in
  let expected_terms = [
                        "@eq listnat (rev (app x y)) (app (rev y) (rev x))";
                        "rev (app x y)";
                        "app x y";
                        "app (rev y) (rev x)";
                        "rev y";
                        "rev x";
                       ]
  in let _, term_matches = List.fold_left (fun (index, matches) t ->
                                           index + 1, matches && 
                                           (String.equal (Sexp.string_of_sexpr t) 
                                                         (List.nth expected_terms index)
                                           )
                                          ) (0, true) terms
  in let matches = (atoms = expected_atoms) && term_matches
  in Alcotest.(check bool) "collected correct terms and atoms from state" true matches


let collect_heuristic_atoms () =
  let all_atoms = ["@eq"; "Nil"; "listnat"; "0"; "app"]
  in let all_terms = []
  in let atom_type_table = Hashtbl.create 3
  in Hashtbl.add atom_type_table "@eq" "forall (A : Type) (_ : A) (_ : A), Prop";
  Hashtbl.add atom_type_table "Nil" "listnat";
  Hashtbl.add atom_type_table "0" "nat";
  Hashtbl.add atom_type_table "listnat" "Set";
  Hashtbl.add atom_type_table "nat" "Set";
  let heuristic_terms = Abstract_NoDup.add_heuristic_atoms all_atoms all_terms atom_type_table []
  in let expected_heuristic_terms = ["0"; "Nil"]
  in
  let _, matches = List.fold_left (fun (index, matches) t ->
                                          index + 1, matches && 
                                          (String.equal (Sexp.string_of_sexpr t) 
                                                        (List.nth expected_heuristic_terms index)
                                          )
                                   ) (0, true) heuristic_terms
  in Alcotest.(check bool) "collected correct heuristic atoms" true matches

let collect_generalizable_terms () = 
  let all_terms = [
                   Sexp.of_string "(Natnil)";
                   Sexp.of_string "(Natcons n Natnil)";
                   Sexp.of_string "(rev x)";
                   Sexp.of_string "(listnat)";
                   Sexp.of_string "(app (rev x) (rev y))";
                  ]
  in let atom_type_table = Hashtbl.create 3
  in Hashtbl.add atom_type_table "(Natnil)" "listnat";
  Hashtbl.add atom_type_table "(listnat)" "Type";
  let expr_type_table = Hashtbl.create 3
  in Hashtbl.add expr_type_table "(Natcons n Natnil)" "listnat";
  Hashtbl.add expr_type_table "(rev x)" "(forall _ : listnat, listnat)";
  let gen_terms = Abstract_NoDup.get_generalizable_terms all_terms expr_type_table atom_type_table
  in
  let expected_gen_terms = [Sexp.of_string "(Natnil)";
                               Sexp.of_string "(Natcons n Natnil)";
                               Sexp.of_string "(rev x)";
                              ]
  in Alcotest.(check bool) "collected correct generalizable terms+atoms" true (gen_terms = expected_gen_terms)

let collect_power_set () =
  let terms = [
                Sexp.of_string "(Natnil)";
                Sexp.of_string "(rev x)";
              ]  
  in let power_set = LatticeUtils.sets terms
  in let expected_power_set = [
                               [Sexp.of_string "(Natnil)"; Sexp.of_string "(rev x)";];
                               [Sexp.of_string "(Natnil)";];
                               [Sexp.of_string "(rev x)";];
                               [];
                              ]
  in Alcotest.(check bool) "collected correct power set" true (expected_power_set = power_set)

let sort_terms () =
  let terms = [Sexp.of_string "(Natnil)"; Sexp.of_string "(app (rev x) (rev y))"; Sexp.of_string "(rev x)";];
  in let sorted_terms = LatticeUtils.sort_by_size terms
  in let expected_sorted_terms = [Sexp.of_string "(app (rev x) (rev y))"; Sexp.of_string "(Natnil)"; Sexp.of_string "(rev x)"; ]
  in Alcotest.(check bool) "sorted terms in descending order" true (expected_sorted_terms = sorted_terms)

let generalize_expr () = 
  let state = "(@eq listnat (rev (app x y)) (app (rev y) (rev x)))"
  in let state_sexp = Sexp.of_string state
  in let terms, atoms = Abstract_NoDup.collect_terms_no_dup [] [] state_sexp
  in let gen_expr = List.nth terms 1
  in let gen, gen_var_name = Generalize_NoDup.generalize_expr state_sexp gen_expr (Utils.next_val (ref 0))
  in let expected_gen = "(@eq listnat lf1 (app (rev y) (rev x)))"
  in let expected_var_name = "lf1"
  in let matches = String.equal expected_gen gen && expected_var_name = gen_var_name
  in Alcotest.(check bool) "goal generalized with expr" true matches

let generalize_expr_list () = 
  let state = "(@eq listnat (rev (app x y)) (app (rev y) (rev x)))"
  in let state_sexp = Sexp.of_string state
  in let terms, atoms = Abstract_NoDup.collect_terms_no_dup [] [] state_sexp
  in let gen_expr = [List.nth terms 1; List.nth terms 4]
  in let expr_type_table = Hashtbl.create 3
  in Hashtbl.add expr_type_table "app (rev y) (rev x)" "(forall (_ : listnat) (_ : listnat), listnat)";
  Hashtbl.add expr_type_table "rev x" "(forall _ : listnat, listnat)";
  Hashtbl.add expr_type_table "rev y" "(forall _ : listnat, listnat)";
  Hashtbl.add expr_type_table "app x y" "(forall (_ : listnat) (_ : listnat), listnat)";
  Hashtbl.add expr_type_table "rev (app x y)" "(forall _ : listnat, listnat)";
  let goal, sigma, vars = Generalize_NoDup.generalize_exprL gen_expr expr_type_table state_sexp
  in let expected_gen = "(@eq listnat lf1 (app lf2 (rev x)))"
  in let expected_var_names = ["lf2"; "lf1"]
  in let expected_sigma = Hashtbl.create 2
  in Hashtbl.add expected_sigma "" "";
  let matches = String.equal expected_gen (Sexp.string_of_sexpr goal) && expected_var_names = vars
  in Alcotest.(check bool) "goal generalized with expr list" true matches

let collect_generalizations () =
  let state = "(@eq listnat (rev (app x y)) (app (rev y) (rev x)))"
  in let state_sexp = Sexp.of_string state
  in let terms, atoms = Abstract_NoDup.collect_terms_no_dup [] [] state_sexp
  in let generalization_set = (LatticeUtils.sets (List.tl terms))
  in let type_table = Hashtbl.create 3
  in Hashtbl.add type_table "app (rev y) (rev x)" "(forall (_ : listnat) (_ : listnat), listnat)";
  Hashtbl.add type_table "@eq listnat (rev (app x y)) (app (rev y) (rev x))" "(forall (_ : listnat) (_ : listnat), listnat)";
  Hashtbl.add type_table "rev x" "(forall _ : listnat, listnat)";
  Hashtbl.add type_table "rev y" "(forall _ : listnat, listnat)";
  Hashtbl.add type_table "app x y" "(forall (_ : listnat) (_ : listnat), listnat)";
  Hashtbl.add type_table "rev (app x y)" "(forall _ : listnat, listnat)";
  Hashtbl.add type_table "listnat" "Set";
  let generalizations = Generalize_NoDup.construct_all_generalizations generalization_set type_table state_sexp
  in let expected_no_gen = 32
  in let is_matches = 32 = (List.length generalizations)
  in Alcotest.(check bool) "goal generalized with expr list" true is_matches

let all = [
  ("test term and atom collection"       ,        `Quick, collect_terms_atoms);
  ("test heuristic atom collection"      ,        `Quick, collect_heuristic_atoms);
  ("test generalizable term collection"  ,        `Quick, collect_generalizable_terms);
  ("test power set collection"           ,        `Quick, collect_power_set);
  ("test generalization of an expression"            ,        `Quick, generalize_expr);
  ("test term sorting in descending order"           ,        `Quick, sort_terms);
  ("test generalization of list of expressions"            ,        `Quick, generalize_expr_list);
  ("test generation of generalizations"            ,        `Quick, collect_generalizations);
]