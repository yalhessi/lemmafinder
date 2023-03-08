open ProofContext

let construct_data_collection vars typs var_typs = 
  let examples,_ = List.fold_left (fun (acc, index) vt -> let pipe = match acc with
                                        | "" -> ""
                                        | _ ->  "++ \"|\" ++"
                                        in let n_var = List.nth vars index
                                        in 
                                        (acc ^ pipe ^ Consts.fmt ("\"%s:\" ++ \"(\" ++ show %s ++ \")\"") n_var n_var), (index+1)
                 ) ("", 0) var_typs
  in let var_string = List.fold_left (fun acc v -> acc ^ " " ^ v) "" (List.tl vars)
  in let var_typs_string = List.fold_left (fun acc v -> acc ^ " " ^ v) "" var_typs
  in let func_signature = Consts.fmt ("Definition collect_data %s :=\n") var_typs_string
  in Consts.fmt ("%s let lfind_var := %s\n in let lfind_v := print %s lfind_var\n in lfind_state lfind_v %s.\n")
  func_signature examples (List.hd vars) var_string

let lfind_extract_examples p_ctxt =
let lfind_content = "
module SS = Set.Make(String)
let values = ref SS.empty
  
let write_to_file value=
  let oc = open_out_gen [Open_append; Open_creat] 0o777 \""^p_ctxt.dir ^"/examples_" ^  p_ctxt.fname ^ ".txt\" in
  if not(SS.mem value !values) then 
    (
      values := SS.add value !values;
      Printf.fprintf oc \"%s\\n\"  value;
    );
  close_out oc; ()

let print n nstr=
  write_to_file (String.of_seq (List.to_seq nstr));
  (n)
  "
in let extract_file_name = Consts.fmt ("%s/%s") p_ctxt.dir "extract.ml"
in FileUtils.write_to_file extract_file_name lfind_content

let generate_example (p_ctxt : ProofContext.proof_context) modules =
  let env = p_ctxt.env in
  let sigma = p_ctxt.sigma in
  let hyps = p_ctxt.hypotheses in
  let current_lemma = ProofContext.get_curr_state_lemma p_ctxt in
  let vars = List.map Names.Id.to_string p_ctxt.all_vars in
  lfind_extract_examples p_ctxt;
  let typs = List.map (fun t -> Utils.get_econstr_str env sigma t) p_ctxt.types in
  let var_typs = ProofContext.get_var_types env sigma hyps in 
  let var_typs = List.map (fun (x,y) -> Consts.fmt ("(%s : %s)") (Names.Id.to_string x) (Utils.get_econstr_str env sigma y)) var_typs in
  let example_file = Consts.fmt ("%s/%s") p_ctxt.dir "lfind_quickchick_generator.v"
  in
  let import_file =
  Consts.fmt "%s\nFrom %s Require Import %s." (Consts.lfind_declare_module) (p_ctxt.namespace) (p_ctxt.fname)  

  in let module_imports = p_ctxt.declarations
  (* List.fold_left (fun acc m -> acc ^ (m ^"\n")) "" modules *)
  in let quickchick_import = Consts.quickchick_import
  in let qc_include = Consts.fmt ("QCInclude \"%s/\".\nQCInclude \".\".") p_ctxt.dir
  
  in let typ_derive = List.fold_left (fun acc t -> acc ^ (TypeUtils.derive_typ_quickchick p_ctxt t)) "" typs

  in let typs_parameter_print = List.fold_left (fun acc t -> match acc with | "" -> t | _ -> acc ^ " -> " ^ t)  "" typs
  in let start_index = ((String.index (List.hd (var_typs)) ':')+1)
  in let end_index = (String.index (List.hd (var_typs)) ')')
  in let hd_parameter = String.sub (List.hd (var_typs)) start_index (end_index - start_index)
  in let parameter_print = Consts.fmt ("Parameter print : %s -> string -> %s.\n") hd_parameter hd_parameter
  
  in let typ_quickchick_content = Consts.fmt ("%s\n%s\n%s\n%s\n%s\n%s\n%s\n%s\n") Consts.lfind_declare_module import_file module_imports current_lemma quickchick_import 
  qc_include Consts.def_qc_num_examples typ_derive
  in let example_print_content = Consts.fmt("%s\n%s%s")  Consts.string_scope parameter_print Consts.extract_print
  in let collect_content = construct_data_collection vars typs var_typs
  in let content = typ_quickchick_content ^ example_print_content ^ collect_content ^ "QuickChick collect_data.\n" ^ Consts.vernac_success
  in FileUtils.write_to_file example_file content;
  let cmd = Consts.fmt "cd %s/ && coqc -R . %s %s" p_ctxt.dir p_ctxt.namespace example_file
  in FileUtils.run_cmd cmd
  