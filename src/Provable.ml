open LatticeUtils
open ProofContext

let generate_lfind_file p_ctxt conjecture count : string =
  let lfind_file = p_ctxt.dir ^ "/lfind" ^ count ^ ".v"
  in let content = p_ctxt.declarations
                ^ "\n Require Import " ^ p_ctxt.fname ^ ".\n" 
                ^ "Lemma " ^ conjecture ^ ".\n"
                ^ "Admitted.\n"
  in FileUtils.write_to_file lfind_file content;
  lfind_file

let check_provable conjecture p_ctxt : bool =
  let lfind_file = generate_lfind_file p_ctxt conjecture.conjecture_str conjecture.conjecture_name
  in Proverbot.run p_ctxt.dir conjecture.conjecture_name

let split_as_provable_non_provable conjectures p_ctxt : conjecture list * conjecture list =
  Proverbot.remove_current_search p_ctxt.dir;
  List.fold_left (fun (true_conj, false_conj) c ->
                                    let is_provable = check_provable c p_ctxt
                                    in if is_provable 
                                        then (c::true_conj, false_conj) 
                                        else (true_conj, c::false_conj)
                    ) ([], []) conjectures