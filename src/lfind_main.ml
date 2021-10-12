open Constr
open Context
open Proofview.Notations
open Sexp
open ProofContext
open Loadpath
open Loc
open Names
open LatticeUtils


exception Invalid_Examples
exception Invalid_MLFile
exception NotFound_MLFile
exception Rewrite_Fail
exception Myth_Fail


let is_ml_generation_success ml_file p_ctxt: bool= 
  if not (Sys.file_exists ml_file) then 
  (
    print_endline("Need to generate file");
    print_endline(ml_file);
    let op = GenerateMLFile.generate_ml_file p_ctxt
    in print_endline (string_of_int (List.length op));
    let is_succ = List.fold_left (fun acc l -> acc || (Utils.contains l "lemmafinder_success") ) false op
    in is_succ
  ) 
  else true

let construct_state_as_lemma gl =
  let goal = Proofview.Goal.concl gl in
  let hyps = Proofview.Goal.hyps gl in
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let hyps, vars, typs, var_typs = 
    List.fold_left (fun (acc_H, acc_V, acc_typs, acc_var_typs) (v, hyp) -> 
                              let var_str = (Names.Id.to_string v)
                              in let hyp_str = (Consts.fmt "(%s:%s)" var_str (Utils.get_exp_str env sigma hyp))
                              in if Utils.contains var_str "H" 
                                then 
                                ( hyp_str::acc_H), acc_V, acc_typs, acc_var_typs
                                else 
                                  let typ_exists = List.fold_left (fun acc t -> acc || (String.equal t (Utils.get_exp_str env sigma hyp))) false acc_typs
                                  in 
                                  let updated_typ = match typ_exists with
                                  | true -> acc_typs
                                  | false -> ((Utils.get_exp_str env sigma hyp)::acc_typs ) 
                                  in 
                                  acc_H, (var_str::acc_V), updated_typ, (hyp_str::acc_var_typs)
                 ) ([],[],[],[]) (Utils.get_hyps hyps)
  in let hyps = List.append var_typs hyps
  in let conc = (Utils.get_exp_str env sigma goal)
  in if List.length hyps == 0 then
     (
       let var_forall = List.fold_left (fun acc v -> acc ^ " " ^ v) "forall" vars
       in (Consts.fmt "Lemma %s:  %s, %s.\nAdmitted." Consts.lfind_lemma var_forall conc), typs, var_typs, vars
     )
    else
    (
      let vars_all = ""
        (* List.fold_left (fun acc v -> acc ^ " " ^ v)  "" vars *)
      in (Consts.fmt "Lemma %s %s %s:%s.\nAdmitted." Consts.lfind_lemma vars_all (String.concat " " hyps) conc), typs, var_typs, vars
    )

let lfind_tac  : unit Proofview.tactic =
  Proofview.Goal.enter
  begin fun gl ->
    let is_running = Utils.get_env_var "is_lfind"
    in 
    if String.equal is_running "true" then Tacticals.New.tclZEROMSG (Pp.str ("Recursive Lfind..Aborting"))
    else
      begin
        let curr_state_lemma, typs, var_typs, vars = construct_state_as_lemma gl
        in print_endline curr_state_lemma;
        let p_ctxt, c_ctxt = construct_proof_context gl
        in Log.stats_log_file := p_ctxt.dir ^ Consts.log_file;
        Log.error_log_file := p_ctxt.dir ^ Consts.error_log_file;
        Log.stats_summary_file := p_ctxt.dir ^ Consts.summary_log_file;
        let module_names = []
          (* Utils.get_modules (p_ctxt.dir ^ "/" ^ p_ctxt.fname ^ ".v") *)
        in 
        let p_ctxt = {p_ctxt with modules = module_names; types = typs}

        (* Generate .ml file and check if it is parsable by myth *)        
        in let ml_file = Consts.fmt "%s/%s_lfind_orig.ml" p_ctxt.dir p_ctxt.fname
        in 
        ( 
        let is_success = is_ml_generation_success ml_file p_ctxt
        in
        if not is_success then raise Invalid_MLFile else 
        (
          if not (Sys.file_exists ml_file) then raise NotFound_MLFile
          else
          (* Now call the library to rewrite the ast *)
          let run_op = GenerateMLFile.run p_ctxt.dir (p_ctxt.fname^"_lfind_orig") p_ctxt.fname
          in let is_success = List.fold_left (fun acc l -> acc || (Utils.contains l "rewrite_success") ) false run_op
          in if not is_success then raise Rewrite_Fail else
          (
            let run_op = Myth.run_parse p_ctxt (p_ctxt.fname^"_wsynth")
            in let is_exception = List.fold_left (fun acc l -> acc || (Utils.contains l "exception") ) false run_op
            in if is_exception then raise Myth_Fail else
            Feedback.msg_info (Pp.str "lemmafinder_ml_generation_success");
          )
        )          
        );

        (* if example file exists use it, else generate examples *)
        let example_file = Consts.fmt "%s/examples_%s.txt" p_ctxt.dir p_ctxt.fname
        in 
        if not (Sys.file_exists example_file) then 
        (
          print_endline "Example file not found, generating";
          let op = GenerateExamples.generate_example p_ctxt typs module_names curr_state_lemma var_typs vars
          in print_endline (string_of_int (List.length op));
          let is_success = List.fold_left (fun acc l -> acc || (Utils.contains l "lemmafinder_success") ) false op
          in
          if not is_success then raise Invalid_Examples else 
          Feedback.msg_info (Pp.str "lemmafinder_example_generation_success")
        )
        else 
        ();

        let coq_examples = Examples.get_examples example_file
        in let ml_examples = Examples.get_ml_examples coq_examples p_ctxt
        in LogUtils.write_tbl_list_to_log coq_examples "Coq Examples";
        LogUtils.write_tbl_list_to_log ml_examples "ML Examples";
        
        let op = FileUtils.run_cmd "export is_lfind=true"
        in let abstraction = Abstract_NoDup.abstract
        in let generalized_terms, conjectures = abstraction p_ctxt c_ctxt
        in 
        (* create a lemma file to use with proverbot *)
        let curr_state_lemma_file = Consts.fmt "%s/%s.v" p_ctxt.dir Consts.lfind_lemma
        in let content = Consts.fmt "%s\nFrom %s Require Import %s.\n %s"
                         p_ctxt.declarations
                         p_ctxt.namespace
                         p_ctxt.fname
                         curr_state_lemma
        in FileUtils.write_to_file curr_state_lemma_file content;
        (* get ml and coq version of the generalized examples *)
        let coq_examples, ml_examples = (ExampleUtils.evaluate_terms generalized_terms coq_examples ml_examples p_ctxt)
        in List.iter (fun c -> LogUtils.write_tbl_to_log c "COQE") coq_examples;
        List.iter (fun c -> LogUtils.write_tbl_to_log c "MLE") ml_examples;
        
        let valid_conjectures, invalid_conjectures = (Valid.split_as_true_and_false conjectures p_ctxt)
        in let cached_lemmas = ref (Hashtbl.create 1000) 
        in List.iter (  
          fun c -> 
          print_endline c.conjecture_name;
          Log.debug (Consts.fmt "Cache size is %d\n" (Hashtbl.length !cached_lemmas));
          (Synthesize.synthesize cached_lemmas p_ctxt ml_examples coq_examples c);
        )
        invalid_conjectures ;
        Log.debug ("Completed Synthesis");
        Stats.summarize !Stats.global_stat curr_state_lemma;
        Log.debug ("COMPLETED LFIND SYNTHESIZER");

        Tacticals.New.tclZEROMSG (Pp.str ("LFIND Successful."))
      end
  end