open Lfindalgo
open ProofContext

let example_dedup () =
  let examples = ["x:(Natnil)|y:(Natnil)|n:(0)";
                  "x:(Natnil)|y:(Natnil)|n:(0)";
                  "x:(Natnil)|y:(Natcons 1 Natnil)|n:(0)";
                 ]
  in let coq_examples = Examples.dedup_examples examples
  in let example_1 = Hashtbl.create 1
  in Hashtbl.add example_1 "x" "(Natnil)";
  Hashtbl.add example_1 "y" "(Natnil)";
  Hashtbl.add example_1 "n" "(0)";
  let example_2 = Hashtbl.create 1
  in Hashtbl.add example_2 "x" "(Natnil)";
  Hashtbl.add example_2 "y" "(Natcons 1 Natnil)";
  Hashtbl.add example_2 "n" "(0)";
  let matches = (List.hd coq_examples = example_2) && (List.nth coq_examples 1 = example_1)
  in Alcotest.(check bool) "examples dedup" true matches

let extract_ml_examples () =
  let example_1 = Hashtbl.create 1
  in Hashtbl.add example_1 "x" "(Natnil)";
  Hashtbl.add example_1 "y" "(Natnil)";
  let example_2 = Hashtbl.create 1
  in Hashtbl.add example_2 "x" "(Natnil)";
  Hashtbl.add example_2 "y" "(Natcons 1 Natnil)";
  let coq_examples = [example_1; example_2]
  in let dir = (List.hd (String.split_on_char '_' (Sys.getcwd ())))
  in let dir = if dir.[(String.length dir) -1] = '/' 
                           then dir
                           else dir ^ "/";
  in let p_ctxt = {
    hypotheses = []; 
    goal = "";
    functions = []; 
    samples = [];
    dir = dir ^ "test/test_rev_append";
    full_context = "";
    fname = "rev_append";
    vars = ["x";"y"];
    namespace = "test";
    declarations = "";
    proof_name = "";
    funcs = [];
    modules = [];
    types = [];
   }
  in let ml_example_1 = Hashtbl.create 1
  in Hashtbl.add ml_example_1 "x" "(  Natnil)";
  Hashtbl.add ml_example_1 "y" "(  Natnil)";
  let ml_example_2 = Hashtbl.create 1
  in
  Hashtbl.add ml_example_2 "x" "(  Natnil)";
  Hashtbl.add ml_example_2 "y" "(  Natcons ((S (O)), Natnil))";
  
  let ml_examples = Examples.get_ml_examples coq_examples p_ctxt 
  in
  let matches = (List.hd ml_examples = ml_example_1) && (List.nth ml_examples 1 = ml_example_2)
  in Alcotest.(check bool) "ml example extraction" true matches

  let all = [
    ("test example dedup"   ,        `Quick, example_dedup);
    ("test ml example extraction"   ,        `Quick, extract_ml_examples);
  ]