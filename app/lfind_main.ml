open Lfindalgo
open ProofContext
open LatticeUtils

exception Invalid_Examples of string

let lfind_tac (debug: bool) (synthesizer: string) : unit Proofview.tactic =
  Consts.start_time := int_of_float(Unix.time ());
  Log.is_debug := debug;
  Proofview.Goal.enter
  begin fun gl ->
    Consts.synthesizer := synthesizer;
    print_endline("The synthesizer used is " ^ !Consts.synthesizer);
    let is_running = Utils.get_env_var "is_lfind"
    in 
    if String.equal is_running "true" then Tacticals.New.tclZEROMSG (Pp.str ("LFind is already running! Aborting"))
    else
      begin
        Utils.env_setup ();
        let p_ctxt = construct_proof_context gl in
        let vars = p_ctxt.vars in
        let typs = p_ctxt.types in
        let contanins_forall = List.exists (Utils.forall_in_hyp) p_ctxt.hypotheses in
        Log.stats_log_file := p_ctxt.dir ^ Consts.log_file;
        Log.error_log_file := p_ctxt.dir ^ Consts.error_log_file;
        Log.stats_summary_file := p_ctxt.dir ^ Consts.summary_log_file;
        
        (* if example file exists use it, else generate examples *)
        let example_file = Consts.fmt "%s/examples_%s.txt" p_ctxt.dir p_ctxt.fname
        in 
        if not (Sys.file_exists example_file) && (List.length vars) > 0 then 
        (
          print_endline "Example file not found, generating";
          if contanins_forall then (print_endline ("Contains forall, and no example file provided. Quickchick does not work with forall");)
          else ();
          (
            let op = GenerateExamples.generate_example p_ctxt   
            in print_endline (string_of_int (List.length op));
            (* 1st check that Quickchick was able to run without error *)
            let ran_successfully = List.fold_left (fun acc l -> acc || (Utils.contains l "lemmafinder_success") ) false op
            (* Then we want to check if Quickchick actually succeeded or if counterexamples were found *)
            (* Quickchick failure message that is printed: *** Failed after _ tests and _ shrinks. *)
            in let quickchick_success = List.fold_left (fun acc l -> acc || (Utils.contains l "+++ Passed 50 tests") ) false op
            in 
            if not ran_successfully then raise (Invalid_Examples "Quickchick failed to run successfully!") else 
            (* if not quickchick_success then raise (Invalid_Examples "Current proof state incorrect (without hypotheses or in general!") else  *)
            Feedback.msg_info (Pp.str "lemmafinder_example_generation_success")
          )
        );
        
        let coq_examples = Examples.dedup_examples (FileUtils.read_file example_file)
        in LogUtils.write_tbl_list_to_log coq_examples "Coq Examples";
        if List.length coq_examples = 0 then raise (Invalid_Examples "No examples found!") else ();
        (* get the current state of the proof *)
        let op = FileUtils.run_cmd "export is_lfind=true"
        in let abstraction = Abstract_NoDup.abstract
        in let generalized_terms, conjectures = abstraction p_ctxt
        in 
        (* create a coq file that has the current stuck state a prover can use *)
        let curr_state_lemma = ProofContext.get_curr_state_lemma p_ctxt in
        let curr_state_lemma_file = Consts.fmt "%s/%s.v" p_ctxt.dir Consts.lfind_lemma
        in let content = Consts.fmt "%s%s\nFrom %s Require Import %s.\n %s"
                         Consts.lfind_declare_module
                         p_ctxt.declarations
                         p_ctxt.namespace
                         p_ctxt.fname
                         curr_state_lemma
        in FileUtils.write_to_file curr_state_lemma_file content;
        Consts.lfind_lemma_content := content;

        (* get ml and coq version of the output of generalized terms *)
        let coq_examples = ExampleUtils.evaluate_terms generalized_terms coq_examples p_ctxt
        in 
        List.iter (fun c -> LogUtils.write_tbl_to_log c "COQE") coq_examples;
        
        let valid_conjectures, invalid_conjectures = (Valid.split_as_true_and_false conjectures p_ctxt)
        in
        let hyp_conjectures = Hypotheses.conjectures_with_hyp invalid_conjectures p_ctxt
        in 
        let hypo_valid_conjectures, _ = (Valid.split_as_true_and_false hyp_conjectures p_ctxt)
        in
        Log.debug (Consts.fmt "no of valid conjectures with hypotheses is %d" (List.length hypo_valid_conjectures));
        let start_time_synth = Unix.time ()
        in
        let cached_lemmas = ref (Hashtbl.create 1000)
        in let cached_exprs = ref (Hashtbl.create 1000)
        in List.iter (
          fun c ->
          let curr_time = int_of_float(Unix.time ())
          in let elapsed_time = curr_time - int_of_float(start_time_synth)
          in print_endline (string_of_int elapsed_time);
          if elapsed_time < 5100 then
          (print_endline c.conjecture_name;
          Log.debug (Consts.fmt "Cache size is %d\n" (Hashtbl.length !cached_lemmas));
          (Synthesize.synthesize cached_exprs cached_lemmas p_ctxt coq_examples c);)
          else ()
        )
        invalid_conjectures ;
        Log.debug ("Completed Synthesis");
        Stats.summarize !Stats.global_stat curr_state_lemma;
        Log.debug ("COMPLETED LFIND SYNTHESIZER");

        Tacticals.New.tclZEROMSG (Pp.str ("LFIND Successful."))
      end
  end