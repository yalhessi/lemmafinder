let parse_example example = 
  let example_tbl = Hashtbl.create 1
  in let split_example = String.split_on_char '|' example
  in List.iter (fun e -> let values = String.split_on_char ':' e
                         in let var_name, value = (List.hd values), (List.hd (List.tl values))
                         in Hashtbl.add example_tbl var_name value;
               ) split_example;
  example_tbl

let dedup_examples (examples: string list) : (string, string) Hashtbl.t list =
  (* 
     Input: All Examples in Coq format from file.
     Output: Dedupes Examples in Coq format (reversed order)
  *)
  let unique_tbl = Hashtbl.create (List.length examples)
  in List.fold_left (fun acc line ->
                          let tbl_line = 
                              try Hashtbl.find unique_tbl line
                              with _ -> -1
                          in if tbl_line < 0 then
                              (
                                Hashtbl.add unique_tbl line 1;
                                (parse_example line)::acc
                              )
                             else
                              acc
                     ) [] examples

let get_example_index examplestr index examples vars_for_synthesis lfind_sigma =
  List.fold_left (fun (examplestr,ind) v ->
                    (* either the var is generalized or original *)
                    let index_example_tbl = (List.nth examples index)
                    in let op = try Hashtbl.find index_example_tbl v
                             with _ ->
                             (
                               let generalized_term, _ = (Hashtbl.find lfind_sigma v)
                               in (Hashtbl.find index_example_tbl (Sexp.string_of_sexpr generalized_term))
                             )
                    in 
                    if ind == ((List.length vars_for_synthesis)-1) then
                    (examplestr ^ op, ind+1)
                    else ((examplestr ^ op ^ " , "), ind+1)
                 ) ("", 0) vars_for_synthesis

let gen_synthesis_examples (examples:(string, string) Hashtbl.t list) 
                           (output_examples: string list)
                           (vars_for_synthesis: string list)
                           (lfind_sigma:(string, Sexp.t list * string) Hashtbl.t)
                           : string list=
  List.mapi (
             fun index op ->
                  let input_str,_ = get_example_index "" index examples vars_for_synthesis lfind_sigma
                  in input_str ^ "=" ^ op ^ ";"
            ) output_examples