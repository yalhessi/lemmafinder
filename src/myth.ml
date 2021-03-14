open ProofContext

let manual_coq_to_ocaml_type typ = 
  if Utils.contains typ "list" then "list" else typ

let get_example_func examples var_types vars =
  let types = List.fold_left (fun acc v -> let updated_typ = manual_coq_to_ocaml_type (try Hashtbl.find var_types v with _ -> "")
                                            in if String.equal "" acc
                                                 then updated_typ
                                                 else acc ^ "-> " ^ updated_typ
                                 ) "" vars
  in let func_dec = "\nlet synth : " ^ types ^ "|>\n"
  in let evidence_list = List.fold_right (fun e acc -> acc ^ "\n" ^ e) examples ""
  in let func = func_dec ^ "{\n" ^ evidence_list ^ "\n}=?"
  in func

let generate_synthesis_file p_ctxt conjecture_name examples var_types vars : string =
  let coq_ml_file = p_ctxt.dir ^ "/" ^ p_ctxt.fname ^ ".ml"
  in let lfind_file = p_ctxt.dir ^ "/" ^ p_ctxt.fname ^ conjecture_name ^ ".ml"
  in let ml_content = List.rev (FileUtils.read_file coq_ml_file)
  in let all_content = (String.concat "\n" ml_content) ^ (get_example_func examples var_types vars)
  in FileUtils.write_to_file lfind_file all_content;
  lfind_file

let enumerate_expressions p_cxt conjecture_name examples var_types vars =
  let synth_file = generate_synthesis_file p_cxt conjecture_name examples var_types vars
  in print_endline ("Written to synth file " ^ synth_file);
