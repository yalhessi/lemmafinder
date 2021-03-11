let parse_example example = 
  let example_tbl = Hashtbl.create 1
  in let split_example = String.split_on_char '|' example
  in List.iter (fun e -> let values = String.split_on_char ':' e
                         in let var_name, value = (List.hd values), (List.hd (List.tl values))
                         in Hashtbl.add example_tbl var_name value;
               ) split_example;
  example_tbl

let get_examples fname =
  let lines = FileUtils.read_file fname
  in let unique_tbl = Hashtbl.create (List.length lines)
  in List.fold_left (fun acc line ->
                          let tbl_line = try Hashtbl.find unique_tbl line with _ -> -1
                          in if tbl_line < 0 then
                              (
                                Hashtbl.add unique_tbl line 1;
                                (parse_example line)::acc
                              )
                             else
                              acc
               ) [] lines

let get_example_index examplestr index examples lfind_var_outputs vars_for_synthesis =
  List.fold_left (fun examplestr v ->
                    let lvar_ops  = (try (Hashtbl.find lfind_var_outputs v) with _ -> [])
                    in match lvar_ops with
                    | [] -> (let op = Hashtbl.find (List.nth examples index) v
                             in examplestr ^ op ^ " => ")
                    | egs -> (let op = List.nth egs index
                    in examplestr ^ op ^ " => ")
                 ) "" vars_for_synthesis
  
let gen_synthesis_examples examples lfind_var_outputs output_examples vars_for_synthesis =
  List.iteri (fun index op -> 
                              let input_str = get_example_index "" index examples lfind_var_outputs vars_for_synthesis
                              in let opstr = input_str ^ op ^ ";"
                              in print_endline opstr
             ) output_examples