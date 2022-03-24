open Lfindalgo

let synthesis_terms () =
  let conjecture = Sexp.of_string "(@eq natural (Succ (len (append y x))) lf1)"
  in let expr_type_table = Hashtbl.create 4
  in Hashtbl.add expr_type_table "(append y x)" "listnat";
  Hashtbl.add expr_type_table "(len (append y x))" "(forall _ : listnat, nat)";
  Hashtbl.add expr_type_table "(Succ (len (append y x)))" "nat";
  let synth_terms = Synthesize.get_terms_to_synthesize [] conjecture ["lf1"] expr_type_table conjecture false
  in
  let matches = String.equal (Sexp.string_of_sexpr (List.nth synth_terms 0)) "Succ (len (append y x))" && String.equal (Sexp.string_of_sexpr (List.nth synth_terms 1)) "lf1"
  in Alcotest.(check bool) "synthesis subterms match" true matches

let vars_of_synthesis () =
  let conjecture = Sexp.of_string "(@eq natural (Succ (len (append y x))) lf1)"
  in let expr_type_table = Hashtbl.create 4
  in Hashtbl.add expr_type_table "(append y x)" "listnat";
  Hashtbl.add expr_type_table "(len (append y x))" "(forall _ : listnat, nat)";
  Hashtbl.add expr_type_table "(Succ (len (append y x)))" "nat";
  let synth_terms = Synthesize.get_terms_to_synthesize [] conjecture ["lf1"] expr_type_table conjecture false
  in
  let vars = Synthesize.get_variables_except_expr conjecture (List.nth synth_terms 1) [] ["y";"x"] ["lf1"]
  in 
  let matches = String.equal (List.nth vars 0) "x" && String.equal (List.nth vars 1) "y"
  in
  Alcotest.(check bool) "synthesis subterms match" true matches

let all = [
  ("test synthesis sub terms"   ,        `Quick, synthesis_terms);
  ("test synthesis variables"   ,        `Quick, vars_of_synthesis);
]