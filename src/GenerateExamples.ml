open ProofContext

let split list n =
  let rec aux i acc = function
    | [] -> List.rev acc, []
    | h :: t as l -> if i = 0 then List.rev acc, l
                     else aux (i - 1) (h :: acc) t 
  in
    aux n [] list

let findi (f : (int -> 'a -> bool)) (l : 'a list) : int*'a =
  let rec findi' n l = match l with
    | [] -> raise Not_found
    | x :: _ when f n x -> (n, x)
    | _ :: l -> findi' (n + 1) l
  in findi' 0 l

let get_first_printable p_ctxt : (int * (Names.Id.t * EConstr.t)) =
  let {env; sigma; hypotheses; var_types; _} : ProofContext.proof_context = p_ctxt in
  let typs = List.map (fun (_, typ) -> Utils.econstr_to_constr typ) var_types in
  let (i,first_non_var) = findi (fun i typ -> not(Constr.isSort typ)) typs in
  (i, List.nth var_types i)
    
let construct_data_collection p_ctxt = 
  let {env; sigma; hypotheses; var_types; _} : ProofContext.proof_context = p_ctxt in
  let vars = List.map Names.Id.to_string p_ctxt.vars in
  let filtered_var_types = List.filter (fun (_, typ) -> not (Constr.isSort (Utils.econstr_to_constr typ))) var_types in
  let var_types_str = List.map (fun (x,y) -> Consts.fmt ("(%s : %s)") (Names.Id.to_string x) (Utils.get_econstr_str env sigma y)) filtered_var_types in

  let examples = List.map (fun (var, typ) -> 
    let var_str = Names.Id.to_string var in
    let show_str = if (Constr.isSort (Utils.econstr_to_constr typ)) then "\"nat\"" else (Consts.fmt "show %s" var_str) in
    (Consts.fmt "\"%s:\" ++ \"(\" ++ %s ++ \")\"" var_str show_str)) var_types |> String.concat "++ \"|\" ++" in
  let (i, first_non_var) = get_first_printable p_ctxt in
  let (first_printable_var, _) = first_non_var in
  let (before_printable_vars, after_printable_vars) = split vars i in

  let var_string = List.fold_left (fun acc v -> acc ^ " " ^ v) "" (List.tl vars)
  in let func_signature = Consts.fmt ("Definition collect_data %s :=\n") (String.concat " " var_types_str)
  in Consts.fmt ("%s let lfind_var := %s\n in let lfind_v := print %s lfind_var\n in lfind_state %s lfind_v %s.\n")
  func_signature examples (Names.Id.to_string first_printable_var)(String.concat " " before_printable_vars) (String.concat " " (List.tl after_printable_vars))

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


let get_notations p_ctxt = 
  List.filter (fun (_,typ) -> Utils.econstr_to_constr typ |> Constr.isSort) p_ctxt.var_types |>
  List.map (fun (var,_) -> Names.Id.to_string var) |>
  List.map (Consts.fmt "Notation %s := nat.\n") |> String.concat "\n"

let get_print_signature (p_ctxt : ProofContext.proof_context) =
  (* print takes and returns the first non-type variable to print the examples *)
  let (i, first_non_var) = get_first_printable p_ctxt in
  let (_, typ) = first_non_var in
  let typ_str = Utils.get_econstr_str p_ctxt.env p_ctxt.sigma typ in
  Consts.fmt ("Parameter print : %s -> string -> %s.\n") typ_str typ_str

let generate_example (p_ctxt : ProofContext.proof_context) =
  lfind_extract_examples p_ctxt;
  let env = p_ctxt.env in
  let sigma = p_ctxt.sigma in
  let hyps = p_ctxt.hypotheses in
  let current_lemma = ProofContext.get_curr_state_lemma p_ctxt in
  let example_file = Consts.fmt ("%s/%s") p_ctxt.dir "lfind_quickchick_generator.v"
  in
  let import_file =
  Consts.fmt "%s\nFrom %s Require Import %s." (Consts.lfind_declare_module) (p_ctxt.namespace) (p_ctxt.fname)  

  in let module_imports = p_ctxt.declarations
  in let quickchick_import = Consts.quickchick_import
  in let qc_include = Consts.fmt ("QCInclude \"%s/\".\nQCInclude \".\".") p_ctxt.dir
  
  in let typ_derive = List.map (TypeUtils.derive_typ_quickchick p_ctxt) p_ctxt.types |> String.concat "\n"


in let parameter_print = get_print_signature p_ctxt
  
  in let typ_quickchick_content = Consts.fmt ("%s\n%s\n%s\n%s\n%s\n%s\n%s\n%s\n") Consts.lfind_declare_module import_file module_imports current_lemma quickchick_import 
  qc_include Consts.def_qc_num_examples typ_derive
  in let notations_content = get_notations p_ctxt 
  in let example_print_content = Consts.fmt("%s\n%s%s")  Consts.string_scope parameter_print Consts.extract_print
  in let collect_content = construct_data_collection p_ctxt
  in let content = typ_quickchick_content ^ notations_content ^ example_print_content ^ collect_content ^ "QuickChick collect_data.\n" ^ Consts.vernac_success
  in FileUtils.write_to_file example_file content;
  let cmd = Consts.fmt "cd %s/ && coqc -R . %s %s" p_ctxt.dir p_ctxt.namespace example_file
  in FileUtils.run_cmd cmd
  