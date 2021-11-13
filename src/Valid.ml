open LatticeUtils
open ProofContext
open Stats

let generate_lfind_file p_ctxt conjecture name : string =
  let lfind_file = p_ctxt.dir ^ "/lfind" ^ name ^ ".v"
  in let module_imports = List.fold_left (fun acc m -> acc ^ (m ^"\n")) "" p_ctxt.modules
  in let typ_derive = List.fold_left (fun acc t -> acc ^ (TypeUtils.derive_typ_quickchick t)) "" p_ctxt.types
  in let content = Consts.fmt "%s\n%s\nFrom %s Require Import %s.\n%s\n%s\nLemma %s.\nAdmitted.\nQuickChick %s.\n"
                   p_ctxt.declarations 
                   Consts.quickchick_import
                   p_ctxt.namespace
                   p_ctxt.fname
                   module_imports
                   typ_derive
                   conjecture
                   name
  in FileUtils.write_to_file lfind_file content;
  lfind_file

let check_validity conjecture p_ctxt : bool =
  let name = conjecture.conjecture_name in
  let lfind_file = generate_lfind_file p_ctxt conjecture.conjecture_str name
  in let is_valid = Quickcheck.run lfind_file p_ctxt.namespace
  in FileUtils.remove_file lfind_file;
  FileUtils.remove_file (p_ctxt.dir ^ "/lfind" ^ name ^ ".glob");
  FileUtils.remove_file (p_ctxt.dir ^ "/lfind" ^ name ^ ".vo");
  FileUtils.remove_file (p_ctxt.dir ^ "/lfind" ^ name ^ ".vok");
  FileUtils.remove_file (p_ctxt.dir ^ "/lfind" ^ name ^ ".vos");
  is_valid

let split_as_true_and_false conjectures p_ctxt : conjecture list * conjecture list =
  List.fold_left (fun (true_conj, false_conj) c ->
                                    let is_valid = check_validity c p_ctxt
                                    in if is_valid 
                                        then 
                                          (
                                            let is_provable = Provable.check_lfind_theorem_add_axiom p_ctxt c.conjecture_name c.conjecture_str
                                            in let is_prover_provable = Provable.check_provable c p_ctxt
                                            in let g_stat = {conjecture = c; is_valid =true; is_provable = is_provable; is_prover_provable = is_prover_provable;
                                            synthesis_stats=[]}
                                            in Log.write_to_log (genstat_to_string g_stat) !Log.stats_log_file;
                                            global_stat := g_stat :: !global_stat;
                                            (c::true_conj, false_conj)
                                          )
                                        else (true_conj, List.append false_conj [c])
                  ) ([], []) conjectures