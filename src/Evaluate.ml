open ProofContext
open ExprUtils
open ExtractToML

let generate_eval_file p_ctxt eval_str : string =
  let lfind_file = p_ctxt.dir ^ "/lfind_eval.v"
  in let content = Consts.fmt "%s\nRequire Import %s.\n%s\n%s"
                   p_ctxt.declarations 
                   p_ctxt.fname
                   Consts.coq_printing_depth
                   eval_str
  in FileUtils.write_to_file lfind_file content;
  lfind_file

let run_eval fname namespace =
  let cmd = "coqc -R . " ^ namespace  ^ " " ^ fname
  in FileUtils.run_cmd cmd

let get_eval_definition expr vars =
  let varstring = List.fold_left (fun acc v -> acc ^ " " ^ v) "" vars 
  in let eval_def = "Definition lfind_eval " ^ varstring
                    ^ ":=\n"
                    ^ (Sexp.string_of_sexpr expr)
                    ^ ".\n"
  in eval_def

let get_compute_string input : string =
  "\nCompute lfind_eval " ^ input ^ ".\n"

let strip str = 
  let str = Str.replace_first (Str.regexp "^ +") "" str in
  Str.replace_first (Str.regexp " +$") "" str

let get_input_string vars example =
  List.fold_left (fun acc v ->
                        acc ^ " " ^ (Hashtbl.find example v)
                 ) "" vars

let get_evaluate_str expr vars examples =
  let expr_vars = get_variables_in_expr expr [] vars
  in let eval_def = get_eval_definition expr expr_vars
  in List.fold_left (fun acc example -> let input = get_input_string expr_vars example
                                        in acc ^ get_compute_string input
                    ) eval_def examples

let get_expr_vals output =
  let val_accm = ref ""
  in List.fold_left (fun acc op -> 
                          if Utils.contains op ":"
                            then 
                            (
                                let updated_acc = ("(" ^ !val_accm ^ ")")::acc
                                in val_accm := "";
                                updated_acc
                            )
                          else 
                            (
                              if Utils.contains op "="
                              then 
                              (
                                val_accm := List.hd (List.rev (String.split_on_char '=' op));
                                acc
                              )
                              else
                              (
                                val_accm := !val_accm ^ op;
                                acc
                              )
                            )
                 ) [] output

let evaluate_coq_expr expr examples p_ctxt =
  let evalstr = get_evaluate_str expr p_ctxt.vars examples
  in let efile = generate_eval_file p_ctxt evalstr
  in let output = run_eval efile p_ctxt.namespace
  in LogUtils.write_list_to_log output "evalresult";
  let expr_output  = get_expr_vals output
  in let names, defs = get_defs_evaluated_examples expr_output
  in let ext_coqfile = generate_ml_extraction_file p_ctxt names defs
  in let output = run_ml_extraction ext_coqfile p_ctxt.namespace
  in let ext_mlfile = Consts.fmt "%s/lfind_extraction.ml" p_ctxt.dir
  in let ext_output = List.rev (FileUtils.read_file ext_mlfile)
  in let extracted_values = get_ml_evaluated_examples ext_output
  in Log.debug (Consts.fmt "length of examples %d\n" (List.length examples));
  Log.debug (Consts.fmt "length of extracted examples %d\n" (List.length extracted_values));
  List.iter (fun e -> Log.debug (Consts.fmt "Val: %s" (e))) extracted_values;
  extracted_values
