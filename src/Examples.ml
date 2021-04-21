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

let get_ml_examples examples p_ctxt =
  List.fold_left (fun acc e ->
                      let names, defs = ExtractToML.get_defs_input_examples e
                      in let ext_coqfile = ExtractToML.generate_ml_extraction_file p_ctxt names defs
                      in let output = ExtractToML.run_ml_extraction ext_coqfile p_ctxt.namespace
                      in let ext_mlfile = Consts.fmt "%s/lfind_extraction.ml" p_ctxt.dir
                      in let ext_output = List.rev (FileUtils.read_file ext_mlfile)
                      in let extracted_values = ExtractToML.get_ml_input_examples ext_output
                      in Hashtbl.iter (fun k v -> Log.debug (Consts.fmt "Val: %s -> %s" k v)) extracted_values;
                      List.append acc [extracted_values]
                 ) [] examples

let get_example_index examplestr index examples lfind_var_outputs vars_for_synthesis =
  List.fold_left (fun examplestr v ->
                    let lvar_ops  = (try (Hashtbl.find lfind_var_outputs v) with _ -> [])
                    in
                    match lvar_ops with
                    | [] -> (
                             let op = Hashtbl.find (List.nth examples index) v
                             in examplestr ^ op ^ " => "
                            )
                    | egs -> (
                              let op = List.nth egs index
                              in examplestr ^ op ^ " => "
                             )
                 ) "" vars_for_synthesis

let gen_synthesis_examples examples lfind_var_outputs output_examples vars_for_synthesis =
  List.mapi (
             fun index op ->
                  let input_str = get_example_index "" index examples lfind_var_outputs vars_for_synthesis
                  in 
                  if Int.equal 0 index then input_str ^ op else input_str ^ op ^ ";"
            ) output_examples