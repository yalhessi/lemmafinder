open Lfindalgo
open OUnit2

(* Testing Generalization for the motivating example
  input file : motivating_example/list_rev.v
  function tested : Generalize_NoDup.construct_all_generalizations *)

(* ===================================================================================================================== *)
(* Hard coded inputs for the generalization function (based on motivating_example/list_rev.v) *)
let goal_sexp = 
  (* "(@eq lst (rev (append (rev x) (Cons n Nil))) (Cons n x))" *)
  [
    Sexp.Expr 
    [
      Sexp.Atom "@eq"; 
      Sexp.Atom "lst"; 
      Sexp.Expr [
        Sexp.Atom "rev"; 
        Sexp.Expr [
          Sexp.Atom "append"; 
          Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; 
          Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]]];
      Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"]
    ]
  ]
let hyps = 
  (* ["(@eq lst (rev (rev x)) x)"] *)
  [
    Sexp.Expr 
    [
      Sexp.Atom "@eq"; 
      Sexp.Atom "lst"; 
      Sexp.Expr [
        Sexp.Atom "rev"; 
        Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]];
      Sexp.Atom "x"
    ]
  ] :: []
let terms = 
  [
    [Sexp.Atom "Nil"];
    [Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];];
    [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];
    [Sexp.Atom "rev"; Sexp.Atom "x"];
    [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"];
    [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"]
  ]
let generalization_set = (LatticeUtils.sets terms)
let type_table_content = 
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
    ("rev ==> forall _ : lst", "lst")
  ]
let type_table = 
  let tt = Hashtbl.create 20 in
  let add_to_table (id : string) (typ : string) = Hashtbl.add tt id typ in
    List.iter (fun (x,y) -> add_to_table x y) type_table_content; tt

(* ===================================================================================================================== *)
(* Helper fucntion to create a hashtable (for the expected results) *)
let make_hash (n : int) (values : (string * (Sexp.t list * string)) list) =
  let tbl = Hashtbl.create n in
  let add_to_table (id : string) (typ : (Sexp.t list * string)) = Hashtbl.add tbl id typ in
    List.iter (fun (x,y) -> add_to_table x y) values; tbl 

(* Hard coded results that are expected from generalization *)
let expected_results = 
  [
    (Sexp.of_string "(@eq lst lf1 lf2)",
    make_hash 2 
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);
    
    (Sexp.of_string "(@eq lst lf1 (Cons n x))",
    make_hash 2 
    [
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst lf1 lf2)",
    make_hash 2 
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst lf1 (Cons n x))",
    make_hash 2 
    [
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst lf1 lf2)",
    make_hash 2 
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);
    
    (Sexp.of_string "(@eq lst lf1 (Cons n x))",
    make_hash 2 
    [
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst lf1 lf2)",
    make_hash 2 
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);
    
    (Sexp.of_string "(@eq lst lf1 (Cons n x))",
    make_hash 2 
    [
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst lf1 lf2)",
    make_hash 2 
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);
    
    (Sexp.of_string "(@eq lst lf1 (Cons n x))",
    make_hash 2 
    [
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst lf1 lf2)",
    make_hash 2 
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);
    
    (Sexp.of_string "(@eq lst lf1 (Cons n x))",
    make_hash 2 
    [
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst lf1 lf2)",
    make_hash 2 
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);
    
    (Sexp.of_string "(@eq lst lf1 (Cons n x))",
    make_hash 2 
    [
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst lf1 lf2)",
    make_hash 2 
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);
    
    (Sexp.of_string "(@eq lst lf1 (Cons n x))",
    make_hash 2 
    [
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);  
    
    (Sexp.of_string "(@eq lst (rev lf1) lf2)",
    make_hash 2 
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]],"(forall (_ : lst) (_ : lst), lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst (rev lf1) (Cons n x))",
    make_hash 2 
    [
      ("lf1", 
      ([Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]],"(forall (_ : lst) (_ : lst), lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst (rev lf1) lf2)",
    make_hash 2 
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]],"(forall (_ : lst) (_ : lst), lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst (rev lf1) (Cons n x))",
    make_hash 2 
    [
      ("lf1", 
      ([Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]],"(forall (_ : lst) (_ : lst), lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);
  
    (Sexp.of_string "(@eq lst (rev lf1) lf2)",
    make_hash 2 
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]],"(forall (_ : lst) (_ : lst), lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst (rev lf1) (Cons n x))",
    make_hash 2 
    [
      ("lf1", 
      ([Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]],"(forall (_ : lst) (_ : lst), lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst (rev lf1) lf2)",
    make_hash 2 
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]],"(forall (_ : lst) (_ : lst), lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst (rev lf1) (Cons n x))",
    make_hash 2 
    [
      ("lf1", 
      ([Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]],"(forall (_ : lst) (_ : lst), lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst (rev (append lf3 lf1)) lf2)",
    make_hash 3 
    [
      ("lf3", 
      ([Sexp.Atom "rev"; Sexp.Atom "x"],"(forall _ : lst, lst)"));
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"],"(forall (_ : nat) (_ : lst), lst)"))
    ],
    ["lf3"; "lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev lf3) x)")]);

    (Sexp.of_string "(@eq lst (rev (append lf2 lf1)) (Cons n x))",
    make_hash 3 
    [
      ("lf2", 
      ([Sexp.Atom "rev"; Sexp.Atom "x"],"(forall _ : lst, lst)"));
      ("lf1", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"],"(forall (_ : nat) (_ : lst), lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev lf2) x)")]);

    (Sexp.of_string "(@eq lst (rev (append lf2 (Cons n lf3))) lf1)",
    make_hash 3 
    [
      ("lf3", 
      ([Sexp.Atom "Nil"],"lst"));
      ("lf2", 
      ([Sexp.Atom "rev"; Sexp.Atom "x"],"(forall _ : lst, lst)"));
      ("lf1", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"))
    ],
    ["lf3"; "lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev lf2) x)")]);

    (Sexp.of_string "(@eq lst (rev (append lf1 (Cons n lf2))) (Cons n x))",
    make_hash 3 
    [
      ("lf2", 
      ([Sexp.Atom "Nil"],"lst"));
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Atom "x"],"(forall _ : lst, lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev lf1) x)")]);

    (Sexp.of_string "(@eq lst (rev (append (rev x) lf1)) lf2)",
    make_hash 3 
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"],"(forall (_ : nat) (_ : lst), lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst (rev (append (rev x) lf1)) (Cons n x))",
    make_hash 3 
    [
      ("lf1", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"],"(forall (_ : nat) (_ : lst), lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst (rev (append (rev x) (Cons n lf2))) lf1)",
    make_hash 3 
    [
      ("lf2", 
      ([Sexp.Atom "Nil"],"lst"));
      ("lf1", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst (rev (append (rev x) (Cons n lf1))) (Cons n x))",
    make_hash 3 
    [
      ("lf1", 
      ([Sexp.Atom "Nil"],"lst"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst lf1 lf2)",
    make_hash 2 
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst lf1 (Cons n x))",
    make_hash 2 
    [
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst lf1 lf2)",
    make_hash 2 
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst lf1 (Cons n x))",
    make_hash 2 
    [
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst lf1 lf2)",
    make_hash 2 
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst lf1 (Cons n x))",
    make_hash 2 
    [
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst lf1 lf2)",
    make_hash 2 
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst lf1 (Cons n x))",
    make_hash 2 
    [
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst lf1 lf2)",
    make_hash 2 
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst lf1 (Cons n x))",
    make_hash 2 
    [
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst lf1 lf2)",
    make_hash 2 
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst lf1 (Cons n x))",
    make_hash 2 
    [
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst lf1 lf2)",
    make_hash 2 
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst lf1 (Cons n x))",
    make_hash 2 
    [
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst lf1 lf2)",
    make_hash 2 
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst lf1 (Cons n x))",
    make_hash 2 
    [
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Expr [Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]];],"(forall _ : lst, lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst (rev lf1) lf2)",
    make_hash 2 
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]],"(forall (_ : lst) (_ : lst), lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst (rev lf1) (Cons n x))",
    make_hash 2 
    [
      ("lf1", 
      ([Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]],"(forall (_ : lst) (_ : lst), lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst (rev lf1) lf2)",
    make_hash 2 
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]],"(forall (_ : lst) (_ : lst), lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst (rev lf1) (Cons n x))",
    make_hash 2 
    [
      ("lf1", 
      ([Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]],"(forall (_ : lst) (_ : lst), lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst (rev lf1) lf2)",
    make_hash 2 
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]],"(forall (_ : lst) (_ : lst), lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst (rev lf1) (Cons n x))",
    make_hash 2 
    [
      ("lf1", 
      ([Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]],"(forall (_ : lst) (_ : lst), lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst (rev lf1) lf2)",
    make_hash 2 
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]],"(forall (_ : lst) (_ : lst), lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst (rev lf1) (Cons n x))",
    make_hash 2 
    [
      ("lf1", 
      ([Sexp.Atom "append"; Sexp.Expr [Sexp.Atom "rev"; Sexp.Atom "x"]; Sexp.Expr [Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"]],"(forall (_ : lst) (_ : lst), lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst (rev (append lf3 lf1)) lf2)",
    make_hash 3 
    [
      ("lf3", 
      ([Sexp.Atom "rev"; Sexp.Atom "x"],"(forall _ : lst, lst)"));
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"],"(forall (_ : nat) (_ : lst), lst)"))
    ],
    ["lf3"; "lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev lf3) x)")]);

    (Sexp.of_string "(@eq lst (rev (append lf2 lf1)) (Cons n x))",
    make_hash 3 
    [
      ("lf2", 
      ([Sexp.Atom "rev"; Sexp.Atom "x"],"(forall _ : lst, lst)"));
      ("lf1", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"],"(forall (_ : nat) (_ : lst), lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev lf2) x)")]);

    (Sexp.of_string "(@eq lst (rev (append lf2 (Cons n Nil))) lf1)",
    make_hash 3 
    [
      ("lf2", 
      ([Sexp.Atom "rev"; Sexp.Atom "x"],"(forall _ : lst, lst)"));
      ("lf1", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev lf2) x)")]);

    (Sexp.of_string "(@eq lst (rev (append lf1 (Cons n Nil))) (Cons n x))",
    make_hash 3 
    [
      ("lf1", 
      ([Sexp.Atom "rev"; Sexp.Atom "x"],"(forall _ : lst, lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev lf1) x)")]);

    (Sexp.of_string "(@eq lst (rev (append (rev x) lf1)) lf2)",
    make_hash 3 
    [
      ("lf2", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"));
      ("lf1", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"],"(forall (_ : nat) (_ : lst), lst)"))
    ],
    ["lf2"; "lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst (rev (append (rev x) lf1)) (Cons n x))",
    make_hash 3 
    [
      ("lf1", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "Nil"],"(forall (_ : nat) (_ : lst), lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst (rev (append (rev x) (Cons n Nil))) lf1)",
    make_hash 3 
    [
      ("lf1", 
      ([Sexp.Atom "Cons"; Sexp.Atom "n"; Sexp.Atom "x"],"(forall (_ : nat) (_ : lst), lst)"))
    ],
    ["lf1"],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

    (Sexp.of_string "(@eq lst (rev (append (rev x) (Cons n Nil))) (Cons n x))",
    make_hash 3 [],
    [],
    [(Sexp.of_string "(@eq lst (rev (rev x)) x)")]);

  ]

(* ===================================================================================================================== *)
(* Helper function to compare the results with the expected results from generalizing *)
let compare_gen_result (result : (Sexp.t list * (string, Sexp.t list * string) Hashtbl.t * string list * Sexp.t list list))
(expected : (Sexp.t list * (string, Sexp.t list * string) Hashtbl.t * string list * Sexp.t list list)) : bool =
  let a,b,c,d = result in
  let aa,bb,cc,dd = expected in
  let result = ref true in
  (* Define comparing tables function *)
  let compare_hash_table (key : string) ((sexp, str) : Sexp.t list * string) =
    try 
      let exp_sexp, exp_str = Hashtbl.find bb key in
      result := !result && (String.equal exp_str str) && (Sexp.equal exp_sexp sexp);
    with Not_found -> result := false
  (* Run the comparison of the hash tables *)
  in Hashtbl.iter compare_hash_table b;
  (* Compare first element *)
  let compare_first_element = Sexp.equal a aa in
  (* Compare the third element *)
  let compare_third_element = ((List.length c) = (List.length cc)) && List.fold_left (&&) true (List.map2 String.equal c cc) in
  (* Compare the last element in tuple *)
  let compare_last_element = ((List.length d) = (List.length dd)) && List.fold_left (&&) true (List.map2 Sexp.equal d dd) in
  (* Package result to return *)
  compare_first_element && !result && compare_third_element && compare_last_element

(* Helper function for the testing driver *)
let test_helper () =
  let results = Generalize_NoDup.construct_all_generalizations generalization_set type_table goal_sexp hyps in
  if (List.length results = List.length expected_results)
    then 
      let rec compare_results = function
      | [], [] -> true
      | h :: t, h_exp :: t_exp -> (compare_gen_result h h_exp) && (compare_results (t,t_exp))
      | _, _ -> false
    in ((compare_results (results, expected_results)), "Current function not behaving as expected.")
  else (if (List.length results > List.length expected_results) 
          then (false, "More results generated than expected.")
          else (false, "Missing expected results (less generated than expected)."))

(* Driver function *)
let test () =
  print_endline ("# of Generalizations Compared: " ^ (string_of_int (List.length expected_results)));
  match test_helper () with
  | (success,msg) -> "testing generalization" >:: (fun _ -> assert_bool msg success)