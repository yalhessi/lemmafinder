open ProofContext
open FileUtils

let generate_ml_file p_ctxt conjecture_name expr: string =
  let coq_ml_file = Consts.fmt "%s/%s.ml" p_ctxt.dir p_ctxt.fname
  in let lfind_file = Consts.fmt "%s/%s%s_coqofml.ml" p_ctxt.dir p_ctxt.fname  conjecture_name
  in let ml_content = List.rev (FileUtils.read_file coq_ml_file)
  in let all_content = Consts.fmt "%s\n\n%s" (String.concat "\n" ml_content) expr
  in FileUtils.write_to_file lfind_file all_content;
  lfind_file

let run ml_fname p_ctxt conjecture_name =
  let coqofocaml_path = Utils.get_env_var "COQOFOCAML"
  in let coqofocaml_output_path = Consts.fmt "%s/%s%s_coqofml.v" p_ctxt.dir p_ctxt.fname  conjecture_name
  in let coqofocaml_cmd = Consts.fmt  "%s %s -output %s" coqofocaml_path ml_fname coqofocaml_output_path
  in let run_coqofocaml = run_cmd (Consts.fmt "%s"  coqofocaml_cmd)
  in List.rev (read_file coqofocaml_output_path)

let get_synth_expr coq_defs =
  let start_accum = ref false
  in let val_accum = ref ""
  in List.fold_left (fun acc l ->
                      if Utils.contains l "Definition synth" 
                      then
                      (
                        val_accum := List.hd (List.rev (String.split_on_char '=' l));
                        start_accum := true;
                        if Utils.contains l "."
                        then 
                        (
                          val_accum := List.hd (String.split_on_char '.' !val_accum);
                          !val_accum
                        ) 
                        else
                        acc
                      )
                      else
                      (
                        if Utils.contains l "." && !start_accum
                        then
                        (
                          if Utils.contains l "="
                          then 
                          (
                            val_accum := List.hd (List.rev (String.split_on_char '=' l));
                            val_accum := List.hd (String.split_on_char '.' !val_accum);
                            !val_accum
                          )
                          else
                          (
                            val_accum := List.hd (String.split_on_char '.' l);
                            !val_accum
                          )
                        ) 
                        else
                        (
                          val_accum := !val_accum ^ l;
                          acc
                        )
                      )
                 ) "" coq_defs

let get_coq_of_expr  p_ctxt conjecture_name expr =
  Log.debug(Consts.fmt "original_expr is :%s" expr);
  let ml_file = generate_ml_file p_ctxt conjecture_name expr
  in let coq_defs = run ml_file p_ctxt conjecture_name
  (* in LogUtils.write_list_to_log coq_defs "Coq Defs"; *)
  in let coq_expr = get_synth_expr coq_defs
  in Log.debug (Consts.fmt "coq_expr is :%s" coq_expr);
  coq_expr

let get_coq_exprs exprs p_ctxt conjecture_name =
  let count = ref 0
  in List.fold_right ( fun e acc ->
                                  if Utils.next_val count () > 15 then acc
                                  else (get_coq_of_expr p_ctxt conjecture_name e) :: acc
                     ) exprs []