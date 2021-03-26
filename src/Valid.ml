open LatticeUtils
open ProofContext
open Stats

let generate_lfind_file p_ctxt conjecture name : string =
  let lfind_file = p_ctxt.dir ^ "/lfind" ^ name ^ ".v"
  in let content = p_ctxt.declarations 
                ^ "\n From QuickChick Require Import QuickChick.\n"
                ^ "Require Import " ^ p_ctxt.fname ^ ".\n" 
                ^ "Lemma " ^ conjecture ^ ".\n"
                ^ "Admitted.\n"
                ^ "QuickChick " ^ name ^ ".\n"
  in FileUtils.write_to_file lfind_file content;
  lfind_file

let check_validity conjecture p_ctxt : bool =
  let lfind_file = generate_lfind_file p_ctxt conjecture.conjecture_str conjecture.conjecture_name
  in Quickcheck.run lfind_file p_ctxt.namespace

let split_as_true_and_false conjectures p_ctxt : conjecture list * conjecture list =
  List.fold_left (fun (true_conj, false_conj) c ->
                                    let is_valid = check_validity c p_ctxt
                                    in if is_valid 
                                        then 
                                          (
                                            let is_provable = Provable.check_lfind_theorem_add_axiom p_ctxt c.conjecture_str
                                            in let g_stat = {conjecture = c; is_valid =true; is_provable = is_provable; synthesis_stats=[]}
                                            in Log.write_to_log (genstat_to_string g_stat) !Log.stats_log_file;
                                            global_stat := g_stat :: !global_stat;
                                            (c::true_conj, false_conj)
                                          )
                                        else (true_conj, List.append false_conj [c])
                  ) ([], []) conjectures