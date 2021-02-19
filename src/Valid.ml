open LatticeUtils
open ProofContext

let generate_lfind_file p_ctxt conjecture name : string =
  let lfind_file = p_ctxt.dir ^ "/lfind" ^ name ^ ".v"
  in FileUtils.remove_file lfind_file;
  let content = "From QuickChick Require Import QuickChick.\n"
                ^ "Require Import " ^ p_ctxt.fname ^ ".\n" 
                ^ "Lemma " ^ conjecture ^ ".\n"
                ^ "Admitted.\n"
                ^ "QuickChick " ^ name ^ ".\n"
  in let oc = open_out lfind_file in
  Printf.fprintf oc "%s" content;
  close_out oc;
  lfind_file

let check_validity conjecture p_ctxt : bool =
  let lfind_file = generate_lfind_file p_ctxt conjecture.conjecture_str conjecture.conjecture_name
  in Quickcheck.run p_ctxt.dir conjecture.conjecture_name

let split_as_true_and_false conjectures p_ctxt : conjecture list * conjecture list =
  List.fold_left (fun (true_conj, false_conj) c ->
                                    let is_provable = check_validity c p_ctxt
                                    in if is_provable 
                                        then (c::true_conj, false_conj) 
                                        else (true_conj, c::false_conj)
                    ) ([], []) conjectures