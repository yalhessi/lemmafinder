open LatticeUtils
open ProofContext
open Stats

let generate_lfind_file (p_ctxt: proof_context)
                        (conjecture: string)
                        (name: string) : string =
  let lfind_file = p_ctxt.dir ^ "/lfind" ^ name ^ ".v"
  in let module_imports = List.fold_left (fun acc m -> acc ^ (m ^"\n")) "" p_ctxt.modules
  in let typs = List.map (Utils.get_econstr_str p_ctxt.env p_ctxt.sigma) p_ctxt.types |> Utils.dedup_list
  in let typ_derive = List.fold_left (fun acc t -> acc ^ (TypeUtils.derive_typ_quickchick p_ctxt t)) "" typs
  in let content = Consts.fmt "%s%s\n%s\nFrom %s Require Import %s.\n%s\n%s\nLemma %s.\nAdmitted.\nQuickChick %s.\n"
                   Consts.lfind_declare_module
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

let check_validity (conjecture: conjecture)
                   (p_ctxt: proof_context) 
                   : bool * string list =
  let name = conjecture.conjecture_name in
  let lfind_file = generate_lfind_file p_ctxt conjecture.conjecture_str name
  in let is_valid, cgs = Quickcheck.run lfind_file p_ctxt.namespace p_ctxt.dir
  in
  is_valid, cgs

let validity_stats conjectures p_ctxt =
    let n_cores = (Utils.cpu_count () / 2)
    in Parmap.parmap ~ncores:n_cores
                       (
                          fun c -> let is_valid, cgs = check_validity c p_ctxt 
                          in let g_stat = {
                                             conjecture = c;
                                             is_valid =is_valid;
                                             is_provable = false;
                                             is_prover_provable = false;
                                             synthesis_stats=[];
                                             cgs = cgs
                                          }
                          in g_stat
                       ) (Parmap.L conjectures)

let helpful_lemma_stats stats p_ctxt = 
  let n_cores = (Utils.cpu_count () / 2)
  in Parmap.parmap ~ncores:1
          (
            fun s -> 
            if (s.is_valid) then 
            (
              let is_provable = Provable.check_lfind_theorem_add_axiom p_ctxt s.conjecture.conjecture_name s.conjecture.conjecture_str
              in let s = {s with is_provable = is_provable;}
              in s
            )
            else
            s
          ) (Parmap.L stats)

let lemma_provable_stats stats p_ctxt = 
  let n_cores = (Utils.cpu_count () / 2)
  in Parmap.parmap ~ncores:1
          (
            fun s -> 
            if (s.is_valid) then 
            (
              let is_prover_provable = Provable.check_provable s.conjecture p_ctxt
              in 
              let time_to_p = int_of_float(Unix.time ()) - !Consts.start_time
              in let s = {s with is_prover_provable = is_prover_provable}
              in s, time_to_p
            )
            else
            s,0
          ) (Parmap.L stats)

let split_as_true_and_false conjectures p_ctxt : conjecture list * conjecture list =
  (* 
    We can do List.map and generate stats.
    and then return true/false conjectures using fold(thats inexpensive)
  *)
  let stats = validity_stats conjectures p_ctxt
  in
  let can_prove_state_stats = helpful_lemma_stats stats p_ctxt
  in
  let can_prove_conj_stats = lemma_provable_stats can_prove_state_stats p_ctxt
  in
  Proverbot.remove_current_search p_ctxt.dir;
  Provable.remove_axioms p_ctxt.dir;
  Quickcheck.remove_files p_ctxt.dir;
  let valid_conjectures, invalid_conjectures =
      List.fold_left (
                      fun (true_conj, false_conj) (s, time_to_p) ->
                        if s.is_valid then
                        (
                          Log.write_to_log (genstat_to_string s) !Log.stats_log_file;
                          if s.is_prover_provable then
                          (
                            if not !Consts.logged_time_to_cat_1
                            then 
                            (
                              Consts.time_to_category_1 := time_to_p;
                              Consts.logged_time_to_cat_1:= true;
                            );
                          );
                          global_stat := s :: !global_stat;
                          (s.conjecture::true_conj, false_conj)
                        )
                        else 
                        (
                          true_conj, List.append false_conj [{s.conjecture with cgs = s.cgs}]
                        )
                     ) ([], []) can_prove_conj_stats
  in
  valid_conjectures, invalid_conjectures