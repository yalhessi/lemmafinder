open ProofContext
open ExprUtils

let generate_eval_file p_ctxt eval_str : string =
  let lfind_file = p_ctxt.dir ^ "/lfind_eval.v"
  in let content = p_ctxt.declarations 
                   ^ "\n Require Import " ^ p_ctxt.fname ^ ".\n"
                ^ eval_str
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
  List.fold_right (fun op acc -> if Utils.contains op ":" 
                                then acc
                                else 
                                let value = List.hd (List.rev (String.split_on_char '=' op))
                                in ("(" ^ value ^ ")")::acc
                 ) output []

let evaluate_coq_expr expr examples p_ctxt =
  print_endline (Sexp.string_of_sexpr expr);
  let evalstr = get_evaluate_str expr p_ctxt.vars examples
  in let efile = generate_eval_file p_ctxt evalstr
  in let output = run_eval efile p_ctxt.namespace
  in get_expr_vals output