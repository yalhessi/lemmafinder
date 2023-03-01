open ProofContext

let generate_ml_extraction_file (p_ctxt: ProofContext.proof_context)
                                (extraction_names : string)
                                (extracted_defs : string) : string =
  let lfind_file = Consts.fmt "%s/lfind_extraction.v" p_ctxt.dir
  in let extraction_filename = Consts.fmt "\"%s/lfind_extraction.ml\"" p_ctxt.dir
  in let module_imports = List.fold_left (fun acc m -> acc ^ (m ^"\n")) "" p_ctxt.modules
  in let content = Consts.fmt 
                    "%s%s\n 
                    From %s Require Import %s.\n %s\n %s\n %s\n %s\n%s\n 
                    Extraction %s %s."
                    Consts.lfind_declare_module
                    p_ctxt.declarations
                    p_ctxt.namespace
                    p_ctxt.fname
                    module_imports
                    Consts.extraction_import
                    Consts.extract_nat
                    Consts.extract_list
                    extracted_defs
                    extraction_filename
                    extraction_names
  in FileUtils.write_to_file lfind_file content;
  lfind_file

let run_ml_extraction (dir: string) (fname: string) (namespace: string) =
  let cmd = "coqc -R " ^ dir ^ " " ^ namespace  ^ " " ^ fname
  in try FileUtils.run_cmd cmd with _ -> []
  
let build_def example def_name =
  Consts.fmt "Definition %s := %s.\n" def_name example

let get_defs_evaluated_examples examples =
  let count = ref 0
  in List.fold_left (fun (names, defs) e -> 
                        let name = Consts.fmt "lfind_example_%d " ((Utils.next_val count) ())
                        in let def = build_def e name
                        in ( (names ^ name) ,(defs ^ def) )
                    ) ("","") examples

let get_ml_evaluated_examples output =
  let val_accm = ref ""
  in let start_accm = ref false
  in let acc = List.fold_left ( fun acc op -> 
                      if Utils.contains op "val" && !start_accm
                      then
                      (
                        let updated_acc = ("(" ^ !val_accm ^ ")")::acc
                        in val_accm := "";
                        start_accm := false;
                        updated_acc
                      )
                      else
                      (
                        if Utils.contains op "let lfind_example" then
                        (
                          val_accm := List.hd (List.rev (String.split_on_char '=' op));
                          start_accm := true;
                          acc
                        )
                        else
                        (
                          if !start_accm 
                          then
                          (
                            val_accm := !val_accm ^ op;
                            acc 
                          )
                          else(
                            acc
                          )
                        )
                      )
                  )
                  
                [] output
  in if !start_accm then ("(" ^ !val_accm ^ ")")::acc else acc

let get_defs_input_examples (example: (string, string) Hashtbl.t) =
  (* 
    Input: An example table in coq format
    Output: Tuple<extraction names, extraction defintions>
  *)
  Hashtbl.fold ( fun k v (names, defs) -> 
                  let name = Consts.fmt "lfind_example_%s " k
                  in let def = build_def v name
                  in ((names ^ name) ,(defs ^ def))
               ) example ("","")

let get_def_name def =
  let split_def_name = (String.split_on_char ' ' def)
  in List.fold_left ( fun acc l ->
                        if Utils.contains l "lfind_example" then
                        (
                          acc ^ List.hd (List.rev (String.split_on_char '_' l))
                        )
                        else
                        acc
                   ) "" split_def_name
  
let get_ml_input_examples (output: string list) : (string, string) Hashtbl.t=
  (* 
    Input: Extracted ml content as list string
    Output: Example in ML format as a table
  *)
  let example_tbl = Hashtbl.create 1
  in let val_accm = ref ""
  in let start_accm = ref false
  in let def_name = ref ""
  in 
      List.iter ( fun op -> 
                if Utils.contains op "val" && !start_accm
                then
                (
                  Hashtbl.add example_tbl !def_name ("(" ^ !val_accm ^ ")");
                  val_accm := "";
                  start_accm := false;
                  def_name := "";
                )
                else
                (
                  if Utils.contains op "let lfind_example" then
                  (
                    val_accm := List.hd (List.rev (String.split_on_char '=' op));
                    start_accm := true;
                    def_name := get_def_name op;
                  )
                  else
                  (
                    if !start_accm 
                    then
                    (
                      val_accm := !val_accm ^ op;
                    )
                  )
                )
            )
          output;
  if !start_accm then Hashtbl.add example_tbl !def_name ("(" ^ !val_accm ^ ")") else ();
  example_tbl