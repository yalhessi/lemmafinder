open ProofContext

let construct_data_collection vars typs var_typs =
  (* in here, we need to make sure quickchick isn't trying to generate a value of type Type, so we remove the type variable and always instantiate it with nat. *)
  let new_var_typs = List.map CoqType.string_to_coqvartype var_typs in
  let examples, _ =
    List.fold_left
      (fun (acc, index) vt ->
        let CoqType.Vartype(name,typ) = vt in
        let pipe = match acc with "" -> "" | _ -> "++ \"|\" ++" in
        let n_var = List.nth vars index in
        let show_str = if (typ == CoqType.Type) then "\"nat\"" else (Consts.fmt "show %s" n_var) in
        ( acc ^ pipe
          ^ (Consts.fmt "\"%s:\" ++ \"(\" ++ %s ++ \")\"" name show_str),
          index + 1 ))
      ("", 0) new_var_typs
  in
  let filtered_var_typs = List.filter (fun t -> match t with
  | (CoqType.Vartype (name, typ)) -> typ != CoqType.Type
  ) new_var_typs in
  let filtered_vars = List.map (fun (CoqType.Vartype (name,typ)) -> name) filtered_var_typs in

  let var_string =
    List.fold_left (fun acc v -> acc ^ " " ^ v) "" (List.tl filtered_vars)
  in
  let var_typs_string =
    List.fold_left (fun acc v -> acc ^ " " ^ v) "" filtered_vars
  in
  let func_signature =
    Consts.fmt "Definition collect_data %s :=\n" var_typs_string
  in
  let type_var_instatiations = String.concat " " (List.map (fun t -> "nat") !CoqType.type_vars) in
  Consts.fmt
    "%s let lfind_var := %s\n\
    \ in let lfind_v := print %s lfind_var\n\
    \ in lfind_state %s lfind_v %s.\n"
    (* in this line, we need to add the type variable instantiations so lfind_state type-checks *)
    func_signature examples (List.hd filtered_vars) type_var_instatiations var_string

let lfind_extract_examples p_ctxt =
  let lfind_content =
    "\n\
     let write_to_file value=\n\
    \  let oc = open_out_gen [Open_append; Open_creat] 0o777 \"" ^ p_ctxt.dir
    ^ "/examples_" ^ p_ctxt.fname
    ^ ".txt\" in\n\
      \  Printf.fprintf oc \"%s\\n\"  value;\n\
      \  close_out oc; ()\n\
       let print n nstr=\n\
      \  write_to_file (String.of_seq (List.to_seq nstr));\n\
      \  (n)\n\
      \  "
  in
  let extract_file_name = Consts.fmt "%s/%s" p_ctxt.dir "extract.ml" in
  FileUtils.write_to_file extract_file_name lfind_content

let instantiate_type_vars () =
  String.concat "\n"
    (List.map (fun t -> Consts.fmt "Notation %s := nat.\n" t) !CoqType.type_vars)

let generate_example p_ctxt typs modules current_lemma var_typs vars =
  let new_var_typs = List.map CoqType.string_to_coqvartype var_typs in
  lfind_extract_examples p_ctxt;
  let example_file =
    Consts.fmt "%s/%s" p_ctxt.dir "lfind_quickchick_generator.v"
  in
  let import_file =
    Consts.fmt "%s\nFrom %s Require Import %s." Consts.lfind_declare_module
      p_ctxt.namespace p_ctxt.fname
  in

  let module_imports =
    p_ctxt.declarations
    (* List.fold_left (fun acc m -> acc ^ (m ^"\n")) "" modules *)
  in
  let quickchick_import = Consts.quickchick_import in
  let qc_include =
    Consts.fmt "QCInclude \"%s/\".\nQCInclude \".\"." p_ctxt.dir
  in
  let vars = List.map CoqType.extract_var_from_var_typ var_typs in
  let typs = List.map CoqType.extract_typ_from_var_typ var_typs in
  print_endline ("tbl Contents of " ^ "typs");
  List.iter (fun k -> print_endline (Consts.fmt "Type -> %s" k)) typs;
  let typs = List.map (fun (CoqType.Vartype(name, typ)) -> typ) new_var_typs in
  let no_dup_typs = Utils.dedup_list typs in
  let typ_derive =
    List.fold_left
      (fun acc t -> acc ^ (TypeUtils.derive_typ_quickchick p_ctxt t))
      "" no_dup_typs
  in
  let typs = List.map CoqType.extract_typ_from_var_typ var_typs in

  (* 1- We can't print type Type
     2- This is a good place to instantiate type variables to nat (Notation typed_var := nat. ) *)
  let typs_parameter_print =
    List.fold_left
      (fun acc t -> match acc with "" -> t | _ -> acc ^ " -> " ^ t)
      "" typs
  in
  let notations_content = instantiate_type_vars () in
  print_endline ("tbl Contents of " ^ "notations_content");
  print_endline notations_content;
  let filtered_var_typs = List.filter (fun t -> match t with
  | (CoqType.Vartype (name, typ)) -> typ != CoqType.Type
  ) new_var_typs in
  print_endline ("tbl Contents of " ^ "filtered_var_typs");
  List.iter (fun k -> print_endline (Consts.fmt "Type -> %s" (CoqType.coqvartype_to_string k))) filtered_var_typs;
  let print_var = CoqType.coqvartype_to_string (List.hd filtered_var_typs) in
  print_endline ("tbl Contents of " ^ "print_var");
  print_endline print_var;
  let start_index = String.index print_var ':' + 1 in
  let end_index = String.index print_var ')' in
  let hd_parameter =
    String.sub print_var start_index (end_index - start_index)
  in
  let parameter_print =
    Consts.fmt "Parameter print : %s -> string -> %s.\n" hd_parameter
      hd_parameter
  in

  let typ_quickchick_content =
    Consts.fmt "%s\n%s\n%s\n%s\n%s\n%s\n%s\n%s\n" Consts.lfind_declare_module
      import_file module_imports current_lemma quickchick_import qc_include
      Consts.def_qc_num_examples typ_derive
  in
  let example_print_content =
    Consts.fmt "%s\n%s%s" Consts.string_scope parameter_print
      Consts.extract_print
  in
  let collect_content = construct_data_collection vars typs var_typs in
  let content =
    typ_quickchick_content ^ notations_content ^ example_print_content ^ collect_content
    ^ "QuickChick collect_data.\n" ^ Consts.vernac_success
  in
  FileUtils.write_to_file example_file content;
  let cmd =
    Consts.fmt "cd %s/ && coqc -R . %s %s" p_ctxt.dir p_ctxt.namespace
      example_file
  in
  Log.debug ("Generating Examples using command: " ^ cmd);
  FileUtils.run_cmd cmd
