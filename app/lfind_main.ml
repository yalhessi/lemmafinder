open Constr
open Context
open Proofview.Notations
open Lfindalgo
open Sexp
open ProofContext
open Loadpath
open Loc
open Names
open LatticeUtils


exception Invalid_Examples of string
exception Invalid_MLFile of string
exception NotFound_MLFile of string
exception Rewrite_Fail of string
exception Myth_Fail of string
module SS = Set.Make(String);;


let is_ml_generation_success ml_file p_ctxt: bool= 
  if not (Sys.file_exists ml_file) then 
  (
    print_endline("Generating ML version of the .v file");
    print_endline(ml_file);
    let op = GenerateMLFile.generate_ml_file p_ctxt
    in print_endline (string_of_int (List.length op));
    let is_succ = List.fold_left (fun acc l -> acc || (Utils.contains l "lemmafinder_success") ) false op
    in is_succ
  )
  else true

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
        let p_ctxt, c_ctxt = construct_proof_context gl in
        let vars = p_ctxt.vars in
        let typs = p_ctxt.types in
        let contanins_forall = List.exists (Utils.forall_in_hyp) p_ctxt.hypotheses in
        Log.stats_log_file := p_ctxt.dir ^ Consts.log_file;
        Log.error_log_file := p_ctxt.dir ^ Consts.error_log_file;
        Log.stats_summary_file := p_ctxt.dir ^ Consts.summary_log_file;
        (* If myth is chosen as the synthesizer, generate .ml file and check if it is parsable by myth *)
        if String.equal synthesizer "myth" then
        (
          let ml_file = Consts.fmt "%s/%s_lfind_orig.ml" p_ctxt.dir p_ctxt.fname
          in 
          (
          let is_success = is_ml_generation_success ml_file p_ctxt
          in
          if not is_success then raise (Invalid_MLFile "Failed Generating .ml of the .v file") else 
          (
            if not (Sys.file_exists ml_file) then raise (NotFound_MLFile ".ml file of .v not found")
            else
            (* Now call the library to rewrite the ast *)
            let run_op = GenerateMLFile.run p_ctxt.dir (p_ctxt.fname^"_lfind_orig") p_ctxt.fname
            in let is_success = List.fold_left (fun acc l -> acc || (Utils.contains l "rewrite_success") ) false run_op
            in if not is_success then raise (Rewrite_Fail "AST rewriting of .ml file failed!") else
            (
              let run_op = Myth.run_parse p_ctxt (p_ctxt.fname^"_wsynth")
              in let is_exception = List.fold_left (fun acc l -> acc || (Utils.contains l "exception") ) false run_op
              in if is_exception then raise (Myth_Fail "Myth failed to parse .ml file!") else
              Feedback.msg_info (Pp.str "lemmafinder_ml_generation_success");
            )
          )        
          );
        );
        
        (* if example file exists use it, else generate examples *)
        let example_file = Consts.fmt "%s/examples_%s.txt" p_ctxt.dir p_ctxt.fname
        in 
        if not (Sys.file_exists example_file) && (List.length vars) > 0 then 
        (
          print_endline "Example file not found, generating";
          if contanins_forall then (print_endline ("Contains forall, and no example file provided. Quickchick does not work with forall"); exit(0);)
          else
          (
            let op = GenerateExamples.generate_example p_ctxt   
            in print_endline (string_of_int (List.length op));
            let is_success = List.fold_left (fun acc l -> acc || (Utils.contains l "lemmafinder_success") ) false op
            in
            if not is_success then raise (Invalid_Examples "Quickchick failed to generate examples!") else 
            Feedback.msg_info (Pp.str "lemmafinder_example_generation_success")
          )
        );
        
        let coq_examples = Examples.dedup_examples (FileUtils.read_file example_file)
        in LogUtils.write_tbl_list_to_log coq_examples "Coq Examples";
        let ml_examples = if String.equal synthesizer "myth" then
        (
          Examples.get_ml_examples coq_examples p_ctxt
        ) else coq_examples
        in LogUtils.write_tbl_list_to_log ml_examples "ML Examples";
        let op = FileUtils.run_cmd "export is_lfind=true"
        in let abstraction = Abstract_NoDup.abstract
        in let generalized_terms, conjectures = abstraction p_ctxt c_ctxt
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
        let coq_examples, ml_examples = (ExampleUtils.evaluate_terms generalized_terms coq_examples ml_examples p_ctxt)
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
          (Synthesize.synthesize cached_exprs cached_lemmas p_ctxt ml_examples coq_examples c);)
          else ()
        )
        invalid_conjectures ;
        Log.debug ("Completed Synthesis");
        Stats.summarize !Stats.global_stat curr_state_lemma;
        Log.debug ("COMPLETED LFIND SYNTHESIZER");

        Tacticals.New.tclZEROMSG (Pp.str ("LFIND Successful."))
      end
  end