open LatticeUtils
open ProofContext

let generate_lfind_file p_ctxt conjecture c_name =
  let lfind_file = p_ctxt.dir ^ "/lfind" ^ c_name ^ ".v"
  in let module_imports = List.fold_left (fun acc m -> acc ^ (m ^"\n")) "" p_ctxt.modules
  in let content = Consts.fmt "%s%s\nFrom %s Require Import %s.\n%s\nLemma %s.\nAdmitted.\n"
                   Consts.lfind_declare_module
                   p_ctxt.declarations
                   p_ctxt.namespace
                   p_ctxt.fname
                   module_imports
                   conjecture
  in FileUtils.write_to_file lfind_file content; ()

let generate_axiom_file p_ctxt conjecture name : string =
  let axiom_file = p_ctxt.dir ^ "/lfind_axiom_"^ name ^".txt"
  in let content = "Lemma " ^ conjecture ^ ".\n"
  in FileUtils.write_to_file axiom_file content;
  axiom_file

let check_provable conjecture p_ctxt : bool =
  generate_lfind_file p_ctxt conjecture.conjecture_str conjecture.conjecture_name; 
  let fname = " lfind" ^ conjecture.conjecture_name ^".v "
  in Proverbot.run p_ctxt.dir conjecture.conjecture_name fname ""

let split_as_provable_non_provable (conjectures: conjecture list)
                                   (p_ctxt : proof_context)
                                   : conjecture list * conjecture list =
  Proverbot.remove_current_search p_ctxt.dir;
  let n_cores = (Utils.cpu_count () / 2)
  in let res = Parmap.parmap ~ncores:1 
                     (fun c -> 
                          let is_provable = check_provable c p_ctxt
                          in let time_to_p = int_of_float(Unix.time ()) - !Consts.start_time;
                          in is_provable, time_to_p, c
                     )
                     (Parmap.L conjectures)
  in List.fold_left (fun (true_conj, false_conj) (is_provabable, time_to_p, c) -> 
                          if is_provabable
                          then
                          (
                            if not !Consts.logged_time_to_cat_1
                            then 
                            (
                              Consts.time_to_category_1 := time_to_p;
                              Consts.logged_time_to_cat_1:= true;
                            );
                            (c::true_conj, false_conj)
                          )
                          else 
                          (
                            (true_conj, c::false_conj)
                          )
                    ) ([], []) res

let remove_axioms prelude =
  let cmd = "rm -rf " ^ prelude ^ "/lfind_axiom*"
  in let cmd_op = FileUtils.run_cmd cmd
  in ()

let check_lfind_theorem_add_axiom p_ctxt proof_name additional_conj : bool =
  let axiom_file = generate_axiom_file p_ctxt additional_conj proof_name
  in let curr_state_lemma_file = Consts.fmt "%s/%s%s.v" p_ctxt.dir Consts.lfind_lemma proof_name
  in
  FileUtils.write_to_file curr_state_lemma_file !Consts.lfind_lemma_content;
  let fname = Consts.lfind_lemma ^proof_name ^ ".v"
  in Proverbot.run p_ctxt.dir proof_name fname axiom_file