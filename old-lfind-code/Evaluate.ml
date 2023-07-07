open ProofContext
open ExprUtils

let generate_eval_file p_ctxt eval_str : string =
  let lfind_file = p_ctxt.dir ^ "/lfind_eval.v"
  in let content = Consts.fmt "%s%s\nFrom %s Require Import %s.\n%s\n%s\n%s\n%s\n%s"
                   Consts.lfind_declare_module
                   p_ctxt.declarations
                   p_ctxt.namespace 
                   p_ctxt.fname
                   ""
                   Consts.coq_printing_depth
                   "Unset Printing Notations." 
                   "Set Printing Implicit."
                   eval_str
  in FileUtils.write_to_file lfind_file content; 
  lfind_file

let run_eval dir fname namespace =
  let cmd = "coqc -R " ^ dir ^ " " ^ namespace  ^ " " ^ fname
  in try FileUtils.run_cmd cmd with _ -> []

let get_eval_definition expr vars (var_typs:(string, string) Hashtbl.t)=
  let var_string = match Hashtbl.length var_typs with
                  | 0 -> List.fold_left (fun acc v -> acc ^ " " ^ v) "" vars 
                  | _ -> List.fold_left (fun acc v -> acc ^ " " ^ "(" ^ v ^ " : " ^ ((Hashtbl.find var_typs v)) ^")") "" vars 
  in let eval_def = "Definition lfind_eval " ^ var_string
                    ^ ":=\n"
                    ^ (Sexp.string_of_sexpr expr)
                    ^ ".\n"
  in eval_def

let get_compute_string input : string =
  "\nCompute lfind_eval " ^ input ^ ".\n"

(* Either the variable is from the original statement or it is a generalized variable which can be found from the expr mapping *)
let get_input_string vars example lfind_sigma =
  (* print_endline "vars";
  List.iter (fun x -> print_endline x) vars;
  print_endline "examples";
  Hashtbl.iter (fun x y -> print_endline (x ^ " - " ^ y)) example;
  print_endline "sigma";
  Hashtbl.iter (fun x (y,_) -> print_endline (x ^ " - " ^ (Sexp.string_of_sexpr y))) lfind_sigma; *)
  List.fold_left (fun acc v ->
                        let v_example = try (Hashtbl.find example v) 
                                        with _ -> let generalized_term,_ = (Hashtbl.find lfind_sigma v)
                                                  in (Hashtbl.find example (Sexp.string_of_sexpr generalized_term))
                        in acc ^ " " ^ v_example
                 ) "" vars

let get_evaluate_str expr vars examples lfind_sigma (var_typs:(string, string) Hashtbl.t) =
  let expr_vars = get_variables_in_expr expr [] vars |> List.rev
  in let eval_def = get_eval_definition expr expr_vars var_typs
  in List.fold_left (fun acc example -> let input = get_input_string expr_vars example lfind_sigma
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

let evaluate_coq_expr expr examples p_ctxt all_vars 
(lfind_sigma:(string, Sexp.t list * string) Hashtbl.t) conj
: (string list) =
  let synthesizer = !Consts.synthesizer
  in let var_typs =  match conj with
                  | None -> (Hashtbl.create 0)
                  | Some c -> ExprUtils.get_type_vars c all_vars
  in let evalstr = get_evaluate_str expr all_vars examples lfind_sigma var_typs
  in let efile = generate_eval_file p_ctxt evalstr
  in let output = run_eval p_ctxt.dir efile p_ctxt.namespace
  in List.rev (get_expr_vals output)
