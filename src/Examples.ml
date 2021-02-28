let hard_coded_examples_double =
  let exampletbl1 = Hashtbl.create 1
  in Hashtbl.add exampletbl1 "n" "(P)";
  let exampletbl2 = Hashtbl.create 1
  in Hashtbl.add exampletbl2 "n" "(K (P))";
  let exampletbl3 = Hashtbl.create 1
  in Hashtbl.add exampletbl3 "n" "(K (K (P)))";
  [exampletbl1; exampletbl2; exampletbl3]

let hard_coded_examples =
  let exampletbl1 = Hashtbl.create 1
  in Hashtbl.add exampletbl1 "l" "[]";
  let exampletbl2 = Hashtbl.create 1
  in Hashtbl.add exampletbl2 "l" "[1;2]";
  let exampletbl3 = Hashtbl.create 1
  in Hashtbl.add exampletbl3 "l" "[1;2;3]";
  [exampletbl1; exampletbl2; exampletbl3]

  (* 0 =>  1 => 2 *)
let get_example_index examplestr index examples lfind_var_outputs vars_for_synthesis =
  List.fold_left (fun examplestr v ->
                    let lvar_ops  = (try (Hashtbl.find lfind_var_outputs v) with _ -> [])
                    in match lvar_ops with
                    | [] -> (let op = Hashtbl.find (List.nth examples index) v
                             in examplestr ^ op ^ " => ")
                             (* "( " ^ op ^ "=>") *)
                    | egs -> (let op = List.nth egs index
                    in Printf.printf "Var is %s value is %s\n" v op;
                    examplestr ^ op ^ " => ")
                 ) "" vars_for_synthesis
  
let gen_synthesis_examples examples lfind_var_outputs output_examples vars_for_synthesis =
  List.iteri (fun index op -> 
                              let input_str = get_example_index "" index examples lfind_var_outputs vars_for_synthesis
                              in let opstr = input_str ^ op ^ ")"
                              in print_endline opstr
             ) output_examples