open Lfindalgo
open OUnit2

(* Testing Conjecture Generation for the motivating example
  input file : motivating_example/list_rev.v
  function tested : Generalize_NoDup.get_all_conjectures *)

(* ===================================================================================================================== *)
(* Hard coded inputs for the conjecture generation function (based on motivating_example/list_rev.v) *)
let generalization_input = GeneralizationTest.expected_results
let variables = [Names.Id.of_string "n"; Names.Id.of_string "x"]
let atom_type_table_content = 
  [
    ("append", "forall (_ : lst) (_ : lst), lst");
    ("n", "nat");
    ("@eq","forall (A : Type) (_ : A) (_ : A), Prop");
    ("lst", "Set");
    ("rev", "forall _ : lst, lst");
    ("Nil","lst");
    ("Cons", "forall (_ : nat) (_ : lst), lst");
    ("x","lst")
  ]
let expr_type_table_content = 
  [
    ("Nil","lst");
    ("@eq lst (rev (rev x)) x", "(forall  (lst : Type)  (_ : lst)  (_ : lst) , Prop)");
    ("rev x", "(forall _ : lst, lst)");
    ("n", "nat");
    ("@eq lst (rev (append (rev x) (Cons n Nil))) (Cons n x)", "(forall  (lst : Type)  (_ : lst)  (_ : lst) , Prop)");
    ("Cons", "forall (_ : nat) (_ : lst), lst");
    ("@eq","forall (A : Type) (_ : A) (_ : A), Prop");
    ("lst", "Set");
    ("Cons n Nil", "(forall (_ : nat) (_ : lst), lst)");
    ("rev (rev x)", "(forall _ : lst, lst)");
    ("Cons n x", "(forall (_ : nat) (_ : lst), lst)");
    ("append", "forall (_ : lst) (_ : lst), lst");
    ("append (rev x) (Cons n Nil)", "(forall (_ : lst) (_ : lst), lst)");
    ("x","lst");
    ("rev (append (rev x) (Cons n Nil))", "(forall _ : lst, lst)");
    ("rev", "forall _ : lst, lst")
  ]
let type_table t n = 
  let tt = Hashtbl.create n in
  let add_to_table (id : string) (typ : string) = Hashtbl.add tt id typ in
    List.iter (fun (x,y) -> add_to_table x y) t; tt

let atom_type_table = type_table atom_type_table_content (List.length atom_type_table_content)
let expr_type_table = type_table expr_type_table_content (List.length expr_type_table_content)

(* ===================================================================================================================== *)
(* Hard coded results that are expected from conjecture creation *)
(* Helper fucntion to create a hashtable (for the expected results) *)
let make_hash (n : int) values =
  let tbl = Hashtbl.create n in
  let add_to_table id typ = Hashtbl.add tbl id typ in
    List.iter (fun (x,y) -> add_to_table x y) values; tbl 

(* (vars_with_types : (string * string) list) (atom_table : (string,string) Hashtbl.t)
(all_expr_table : (string,string) Hashtbl.t) (hyps : Sexp.t list list) (lfind_vars : string list) (body_sexp : Sexp.t list)
(name : string) (body : string) (conj_str : string) (sigma : (string, Sexp.t list * string) Hashtbl.t) :  *)
let construct_conjecture (vars_with_types, hyps, lfind_vars, body_sexp, name, body, conj_str, sigma) 
: LatticeUtils.conjecture =
  {
    sigma = sigma; 
    conjecture_str = conj_str;
    conjecture_name = name;
    body = body;
    body_sexp = body_sexp;
    lfind_vars = lfind_vars;
    all_expr_type_table = 
    (* all_expr_types_table *)
    make_hash 8
    [
      ("Nil", "lst");
      ("@eq lst (rev (rev x)) x", "(forall  (lst : Type)  (_ : lst)  (_ : lst) , Prop)");
      ("rev x", "(forall _ : lst, lst)");
      ("n", "nat");
      ("@eq lst (rev (append (rev x) (Cons n Nil))) (Cons n x)", "(forall  (lst : Type)  (_ : lst)  (_ : lst) , Prop)");
      ("Cons", "forall (_ : nat) (_ : lst), lst");
      ("@eq", "forall (A : Type) (_ : A) (_ : A), Prop");
      ("lst", "Set");
      ("Cons n Nil", "(forall (_ : nat) (_ : lst), lst)");
      ("rev (rev x)", "(forall _ : lst, lst)");
      ("Cons n x", "(forall (_ : nat) (_ : lst), lst)");
      ("append", "forall (_ : lst) (_ : lst), lst");
      ("append (rev x) (Cons n Nil)", "(forall (_ : lst) (_ : lst), lst)");
      ("x", "lst");
      ("rev (append (rev x) (Cons n Nil))", "(forall _ : lst, lst)");
      ("rev", "forall _ : lst, lst")
    ];
    atom_type_table = 
    (* all_atom_types_table *)
    make_hash 8
    [
      ("append", "forall (_ : lst) (_ : lst), lst");
      ("n", "nat");
      ("@eq", "forall (A : Type) (_ : A) (_ : A), Prop");
      ("lst", "Set");
      ("rev", "forall _ : lst, lst");
      ("Nil", "lst");
      ("Cons", "forall (_ : nat) (_ : lst), lst");
      ("x", "lst")
    ];
    hyps = hyps;
    cgs = [];
    vars = List.map (fun (x,_) -> x) vars_with_types;
    vars_with_types = vars_with_types;
    normalized_var_map = Hashtbl.create 0;
  }

let expected_conj_contents =
  [
    ((* var_with_types *)
    [("x","lst"); ("n","nat")], 
    (* hyps *)
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")],
    (* lfind_vars *)
    [],
    (* body_sexp *)
    (Sexp.of_string "(@eq lst (rev (append (rev x) (Cons n Nil))) (Cons n x))"),
    (* name *)
    "conj16",
    (* body *)
    ": forall (x : lst) (n : nat) , (@eq lst (rev (append (rev x) (Cons n Nil))) (Cons n x))",
    (* conj_str *)
    "conj16: forall (x : lst) (n : nat) , (@eq lst (rev (append (rev x) (Cons n Nil))) (Cons n x))",
    (* sigma *)
    make_hash 0
    []);

    ((* var_with_types *)
    [("x","lst"); ("n","nat"); ("lf1","lst")], 
    (* hyps *)
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")],
    (* lfind_vars *)
    ["lf1"],
    (* body_sexp *)
    (Sexp.of_string "(@eq lst (rev (append (rev x) (Cons n Nil))) lf1)"),
    (* name *)
    "conj15",
    (* body *)
    ": forall (x : lst) (n : nat) (lf1 : lst) , (@eq lst (rev (append (rev x) (Cons n Nil))) lf1)",
    (* conj_str *)
    "conj15: forall (x : lst) (n : nat) (lf1 : lst) , (@eq lst (rev (append (rev x) (Cons n Nil))) lf1)",
    (* sigma *)
    make_hash 1
    [
      ("lf1", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"))
    ]);

    ((* var_with_types *)
    [("lf1","lst"); ("n","nat"); ("x","lst")], 
    (* hyps *)
    [(Sexp.of_string "(@eq lst (rev lf1) x)")],
    (* lfind_vars *)
    ["lf1"],
    (* body_sexp *)
    (Sexp.of_string "(@eq lst (rev (append lf1 (Cons n Nil))) (Cons n x))"),
    (* name *)
    "conj14",
    (* body *)
    ": forall (lf1 : lst) (n : nat) (x : lst) , (@eq lst (rev (append lf1 (Cons n Nil))) (Cons n x))",
    (* conj_str *)
    "conj14: forall (lf1 : lst) (n : nat) (x : lst) , (@eq lst (rev (append lf1 (Cons n Nil))) (Cons n x))",
    (* sigma *)
    make_hash 1
    [
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Atom "x"],"(forall _ : lst, lst)"));
    ]);

    ((* var_with_types *)
    [("lf2","lst"); ("n","nat"); ("lf1","lst")], 
    (* hyps *)
    [(Sexp.of_string "(@eq lst (rev lf2) x)")],
    (* lfind_vars *)
    ["lf2";"lf1"],
    (* body_sexp *)
    (Sexp.of_string "(@eq lst (rev (append lf2 (Cons n Nil))) lf1)"),
    (* name *)
    "conj13",
    (* body *)
    ": forall (lf2 : lst) (n : nat) (lf1 : lst) , (@eq lst (rev (append lf2 (Cons n Nil))) lf1)",
    (* conj_str *)
    "conj13: forall (lf2 : lst) (n : nat) (lf1 : lst) , (@eq lst (rev (append lf2 (Cons n Nil))) lf1)",
    (* sigma *)
    make_hash 2
    [
      ("lf2", 
      ([Sexp.Atom "rev"; Sexp.Atom "x"],"(forall _ : lst, lst)"));
      ("lf1", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"))
    ]);

    ((* var_with_types *)
    [("x","lst"); ("n","nat"); ("lf1","lst")], 
    (* hyps *)
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")],
    (* lfind_vars *)
    ["lf1"],
    (* body_sexp *)
    (Sexp.of_string "(@eq lst (rev (append (rev x) (Cons n lf1))) (Cons n x))"),
    (* name *)
    "conj12",
    (* body *)
    ": forall (x : lst) (n : nat) (lf1 : lst) , (@eq lst (rev (append (rev x) (Cons n lf1))) (Cons n x))",
    (* conj_str *)
    "conj12: forall (x : lst) (n : nat) (lf1 : lst) , (@eq lst (rev (append (rev x) (Cons n lf1))) (Cons n x))",
    (* sigma *)
    make_hash 2
    [
      ("lf1",
      ([Sexp.Atom "Nil"],"lst"))
    ]);

    ((* var_with_types *)
    [("x","lst"); ("n","nat"); ("lf2","lst"); ("lf1","lst")], 
    (* hyps *)
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")],
    (* lfind_vars *)
    ["lf2";"lf1"],
    (* body_sexp *)
    (Sexp.of_string "(@eq lst (rev (append (rev x) (Cons n lf2))) lf1)"),
    (* name *)
    "conj11",
    (* body *)
    ": forall (x : lst) (n : nat) (lf2 : lst) (lf1 : lst) , (@eq lst (rev (append (rev x) (Cons n lf2))) lf1)",
    (* conj_str *)
    "conj11: forall (x : lst) (n : nat) (lf2 : lst) (lf1 : lst) , (@eq lst (rev (append (rev x) (Cons n lf2))) lf1)",
    (* sigma *)
    make_hash 2
    [
      ("lf2",
      ([Sexp.Atom "Nil"],"lst"));
      ("lf1", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"))
    ]);

    ((* var_with_types *)
    [("x","lst"); ("lf1","lst"); ("n","nat")], 
    (* hyps *)
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")],
    (* lfind_vars *)
    ["lf1"],
    (* body_sexp *)
    (Sexp.of_string "(@eq lst (rev (append (rev x) lf1)) (Cons n x))"),
    (* name *)
    "conj10",
    (* body *)
    ": forall (x : lst) (lf1 : lst) (n : nat) , (@eq lst (rev (append (rev x) lf1)) (Cons n x))",
    (* conj_str *)
    "conj10: forall (x : lst) (lf1 : lst) (n : nat) , (@eq lst (rev (append (rev x) lf1)) (Cons n x))",
    (* sigma *)
    make_hash 2
    [
      ("lf1", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"],"(forall (_ : nat) (_ : lst), lst)"))
    ]);

    ((* var_with_types *)
    [("x","lst"); ("lf1","lst"); ("lf2","lst")], 
    (* hyps *)
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")],
    (* lfind_vars *)
    ["lf2";"lf1"],
    (* body_sexp *)
    (Sexp.of_string "(@eq lst (rev (append (rev x) lf1)) lf2)"),
    (* name *)
    "conj9",
    (* body *)
    ": forall (x : lst) (lf1 : lst) (lf2 : lst) , (@eq lst (rev (append (rev x) lf1)) lf2)",
    (* conj_str *)
    "conj9: forall (x : lst) (lf1 : lst) (lf2 : lst) , (@eq lst (rev (append (rev x) lf1)) lf2)",
    (* sigma *)
    make_hash 2
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"],"(forall (_ : nat) (_ : lst), lst)"))
    ]);

    ((* var_with_types *)
    [("lf1","lst"); ("n","nat"); ("lf2","lst"); ("x","lst")], 
    (* hyps *)
    [(Sexp.of_string "(@eq lst (rev lf1) x)")],
    (* lfind_vars *)
    ["lf2";"lf1"],
    (* body_sexp *)
    (Sexp.of_string "(@eq lst (rev (append lf1 (Cons n lf2))) (Cons n x))"),
    (* name *)
    "conj8",
    (* body *)
    ": forall (lf1 : lst) (n : nat) (lf2 : lst) (x : lst) , (@eq lst (rev (append lf1 (Cons n lf2))) (Cons n x))",
    (* conj_str *)
    "conj8: forall (lf1 : lst) (n : nat) (lf2 : lst) (x : lst) , (@eq lst (rev (append lf1 (Cons n lf2))) (Cons n x))",
    (* sigma *)
    make_hash 2
    [
      ("lf2",
      ([Sexp.Atom "Nil"],"lst"));
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Atom "x"],"(forall _ : lst, lst)"));
    ]);

    ((* var_with_types *)
    [("lf2","lst"); ("n","nat"); ("lf3","lst"); ("lf1","lst")], 
    (* hyps *)
    [(Sexp.of_string "(@eq lst (rev lf2) x)")],
    (* lfind_vars *)
    ["lf3";"lf2";"lf1"],
    (* body_sexp *)
    (Sexp.of_string "(@eq lst (rev (append lf2 (Cons n lf3))) lf1)"),
    (* name *)
    "conj7",
    (* body *)
    ": forall (lf2 : lst) (n : nat) (lf3 : lst) (lf1 : lst) , (@eq lst (rev (append lf2 (Cons n lf3))) lf1)",
    (* conj_str *)
    "conj7: forall (lf2 : lst) (n : nat) (lf3 : lst) (lf1 : lst) , (@eq lst (rev (append lf2 (Cons n lf3))) lf1)",
    (* sigma *)
    make_hash 2
    [
      ("lf3",
      ([Sexp.Atom "Nil"],"lst"));
      ("lf2", 
      ([Sexp.Atom "rev"; Sexp.Atom "x"],"(forall _ : lst, lst)"));
      ("lf1", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"))
    ]);

    ((* var_with_types *)
    [("lf2","lst");  ("lf1","lst"); ("n","nat"); ("x","lst")], 
    (* hyps *)
    [(Sexp.of_string "(@eq lst (rev lf2) x)")],
    (* lfind_vars *)
    ["lf2";"lf1"],
    (* body_sexp *)
    (Sexp.of_string "(@eq lst (rev (append lf2 lf1)) (Cons n x))"),
    (* name *)
    "conj6",
    (* body *)
    ": forall (lf2 : lst) (lf1 : lst) (n : nat) (x : lst) , (@eq lst (rev (append lf2 lf1)) (Cons n x))",
    (* conj_str *)
    "conj6: forall (lf2 : lst) (lf1 : lst) (n : nat) (x : lst) , (@eq lst (rev (append lf2 lf1)) (Cons n x))",
    (* sigma *)
    make_hash 2
    [
      ("lf2", 
      ([Sexp.Atom "rev"; Sexp.Atom "x"],"(forall _ : lst, lst)"));
      ("lf1", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"],"(forall (_ : nat) (_ : lst), lst)"))
    ]);

    ((* var_with_types *)
    [("lf3","lst"); ("lf1","lst"); ("lf2","lst")], 
    (* hyps *)
    [(Sexp.of_string "(@eq lst (rev lf3) x)")],
    (* lfind_vars *)
    ["lf3";"lf2";"lf1"],
    (* body_sexp *)
    (Sexp.of_string "(@eq lst (rev (append lf3 lf1)) lf2)"),
    (* name *)
    "conj5",
    (* body *)
    ": forall (lf3 : lst) (lf1 : lst) (lf2 : lst) , (@eq lst (rev (append lf3 lf1)) lf2)",
    (* conj_str *)
    "conj5: forall (lf3 : lst) (lf1 : lst) (lf2 : lst) , (@eq lst (rev (append lf3 lf1)) lf2)",
    (* sigma *)
    make_hash 2
    [
      ("lf3", 
      ([Sexp.Atom "rev"; Sexp.Atom "x"],"(forall _ : lst, lst)"));
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"],"(forall (_ : nat) (_ : lst), lst)"))
    ]);

    ((* var_with_types *)
    [("lf1","lst"); ("n","nat"); ("x","lst")], 
    (* hyps *)
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")],
    (* lfind_vars *)
    ["lf1"],
    (* body_sexp *)
    (Sexp.of_string "(@eq lst (rev lf1) (Cons n x))"),
    (* name *)
    "conj4",
    (* body *)
    ": forall (lf1 : lst) (n : nat) (x : lst) , (@eq lst (rev lf1) (Cons n x))",
    (* conj_str *)
    "conj4: forall (lf1 : lst) (n : nat) (x : lst) , (@eq lst (rev lf1) (Cons n x))",
    (* sigma *)
    make_hash 2
    [
      ("lf1", 
      ([Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]],"(forall (_ : lst) (_ : lst), lst)"))
    ]);

    ((* var_with_types *)
    [("lf1","lst"); ("lf2","lst")], 
    (* hyps *)
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")],
    (* lfind_vars *)
    ["lf2";"lf1"],
    (* body_sexp *)
    (Sexp.of_string "(@eq lst (rev lf1) lf2)"),
    (* name *)
    "conj3",
    (* body *)
    ": forall (lf1 : lst) (lf2 : lst) , (@eq lst (rev lf1) lf2)",
    (* conj_str *)
    "conj3: forall (lf1 : lst) (lf2 : lst) , (@eq lst (rev lf1) lf2)",
    (* sigma *)
    make_hash 2
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]],"(forall (_ : lst) (_ : lst), lst)"))
    ]);

    ((* var_with_types *)
    [("lf1","lst"); ("n", "nat"); ("x","lst")], 
    (* hyps *)
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")],
    (* lfind_vars *)
    ["lf1"],
    (* body_sexp *)
    (Sexp.of_string "(@eq lst lf1 (Cons n x))"),
    (* name *)
    "conj2",
    (* body *)
    ": forall (lf1 : lst) (n : nat) (x : lst) , (@eq lst lf1 (Cons n x))",
    (* conj_str *)
    "conj2: forall (lf1 : lst) (n : nat) (x : lst) , (@eq lst lf1 (Cons n x))",
    (* sigma *)
    make_hash 2
    [
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ]);

    ((* var_with_types *)
    [("lf1","lst"); ("lf2","lst")], 
    (* hyps *)
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")],
    (* lfind_vars *)
    ["lf2";"lf1"],
    (* body_sexp *)
    (Sexp.of_string "(@eq lst lf1 lf2)"),
    (* name *)
    "conj1",
    (* body *)
    ": forall (lf1 : lst) (lf2 : lst) , (@eq lst lf1 lf2)",
    (* conj_str *)
    "conj1: forall (lf1 : lst) (lf2 : lst) , (@eq lst lf1 lf2)",
    (* sigma *)
    make_hash 2
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ]);
  ]

let expected_results = List.map construct_conjecture expected_conj_contents
  
(* ===================================================================================================================== *)
(* Helper function to compare the results with the expected results from generalizing *)
let compare_conjectures (output : LatticeUtils.conjecture) (expected : LatticeUtils.conjecture) : bool =
  let result = ref true in
  (* Define comparing tables function *)
  let compare_sigma (key : string) ((sexp, str) : Sexp.t list * string) =
    try 
      let exp_sexp, exp_str = Hashtbl.find expected.sigma key in
      result := !result && (String.equal exp_str str) && (Sexp.equal exp_sexp sexp);
    with Not_found -> result := false
  in let compare_type_table (tbl : (string,string) Hashtbl.t) (id : string) (typ : string) =
    try 
      let exp_typ = Hashtbl.find tbl id in
      result := !result && (String.equal exp_typ typ);
    with Not_found -> result := false
  (* Run the comparison of the hash tables *)
  in Hashtbl.iter compare_sigma output.sigma;
  Hashtbl.iter (compare_type_table expected.atom_type_table) output.atom_type_table;
  Hashtbl.iter (compare_type_table expected.all_expr_type_table) output.all_expr_type_table;
  (* Compare conjecture_str *)
  let compare_conj_str = String.equal output.conjecture_str expected.conjecture_str in
  (* Compare conjecture_str *)
  let compare_conj_name = String.equal output.conjecture_name expected.conjecture_name in
  (* Compare conjecture_str *)
  let compare_body = String.equal output.body expected.body in
  (* Compare body_sexp *)
  let compare_body_sexp = Sexp.equal output.body_sexp expected.body_sexp in
  (* Compare lfind_vars *)
  let compare_lfind_vars = ((List.length output.lfind_vars) = (List.length expected.lfind_vars)) && 
    List.fold_left (&&) true (List.map2 String.equal output.lfind_vars expected.lfind_vars) in
  (* Compare hyps *)
  let compare_hyps = ((List.length output.hyps) = (List.length expected.hyps)) && 
    List.fold_left (&&) true (List.map2 Sexp.equal output.hyps expected.hyps) in
  (* Compare vars *)
  let compare_vars = ((List.length output.vars) = (List.length expected.vars)) && 
    List.fold_left (&&) true (List.map2 String.equal output.vars expected.vars) in
  (* Compare vars_with_types *)
  let compare_vars_with_types = ((List.length output.vars_with_types) = (List.length expected.vars_with_types)) && 
    List.fold_left (&&) true 
    (List.map2 
    (fun (x,y) (a,b) -> ((String.equal a x) && (String.equal b y))) 
    output.vars_with_types expected.vars_with_types) in
  (* Package result to return *)
  !result && compare_conj_str && compare_conj_name && compare_body && compare_body_sexp &&
  compare_lfind_vars && compare_hyps && compare_vars && compare_vars_with_types

let rec substring n acc = function
| [] -> acc
| h :: t -> if (n > 0) then substring (n-1) (acc @ [h]) t else acc

(* Helper function for the testing driver *)
let test_helper () =
  let results = Generalize_NoDup.get_all_conjectures generalization_input atom_type_table expr_type_table variables in
  if (List.length results = List.length expected_results)
    then 
      let rec compare_results = function
      | [], [] -> true
      | h :: t, h_exp :: t_exp -> (compare_conjectures h h_exp) && (compare_results (t,t_exp))
      | _, _ -> false
    in ((compare_results (results, expected_results)), "Current function not behaving as expected.")
  else (if (List.length results > List.length expected_results) 
          then (false, "More results generated than expected.")
          else (false, "Missing expected results (less generated than expected)."))

(* Driver function *)
let test () =
  print_endline ("# of Conjectures Compared: " ^ (string_of_int (List.length expected_results)));
  match test_helper () with
  | (success,msg) -> "testing conjecture generation" >:: (fun _ -> assert_bool msg success)