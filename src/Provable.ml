open LatticeUtils
open ProofContext

let generate_lfind_file p_ctxt conjecture c_name =
  let lfind_file = p_ctxt.dir ^ "/lfind" ^ c_name ^ ".v"
  in let module_imports = List.fold_left (fun acc m -> acc ^ (m ^"\n")) "" p_ctxt.modules
  in let content = Consts.fmt "%s\nFrom %s Require Import %s.\n%s\nLemma %s.\nAdmitted.\n"
                   p_ctxt.declarations
                   p_ctxt.namespace
                   p_ctxt.fname
                   module_imports
                   conjecture
  in FileUtils.write_to_file lfind_file content; ()

let generate_axiom_file p_ctxt conjecture : string =
  let axiom_file = p_ctxt.dir ^ "/lfind_axiom.txt"
  in let content = "Lemma " ^ conjecture ^ ".\n"
  in FileUtils.write_to_file axiom_file content;
  axiom_file

let check_provable conjecture p_ctxt : bool =
  generate_lfind_file p_ctxt conjecture.conjecture_str conjecture.conjecture_name; 
  let fname = " lfind" ^ conjecture.conjecture_name ^".v "
  in Proverbot.run p_ctxt.dir conjecture.conjecture_name fname ""

let split_as_provable_non_provable conjectures p_ctxt : conjecture list * conjecture list =
  Proverbot.remove_current_search p_ctxt.dir;
  List.fold_left (fun (true_conj, false_conj) c ->
                                    let is_provable = check_provable c p_ctxt
                                    in if is_provable 
                                        then (c::true_conj, false_conj) 
                                        else (true_conj, c::false_conj)
                    ) ([], []) conjectures

let check_lfind_theorem_add_axiom p_ctxt proof_name additional_conj : bool =
  let axiom_file = generate_axiom_file p_ctxt additional_conj
  in let fname = Consts.lfind_lemma ^ ".v"
  in Proverbot.run p_ctxt.dir proof_name fname axiom_file