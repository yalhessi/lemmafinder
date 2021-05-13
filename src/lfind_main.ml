open Constr
open Context
open Proofview.Notations
open Sexp
open ProofContext
open Loadpath
open Loc
open Names
open LatticeUtils

let construct_state_as_lemma gl =
  let goal = Proofview.Goal.concl gl in
  let hyps = Proofview.Goal.hyps gl in
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let hyps, vars = List.fold_left (fun (acc_H, acc_V) (v, hyp) -> 
                              let var_str = (Names.Id.to_string v)
                              in let hyp_str = [(Consts.fmt "(%s:%s)" var_str (Utils.get_exp_str env sigma hyp))]
                              in if Utils.contains var_str "H" 
                                then 
                                  (List.append acc_H hyp_str), acc_V
                                else 
                                  acc_H,(List.append acc_V [var_str])
                 ) ([],[]) (Utils.get_hyps hyps)
  in let conc = (Utils.get_exp_str env sigma goal)
  in if List.length hyps == 0 then
     (
       let var_forall = List.fold_left (fun acc v -> acc ^ " " ^ v) "forall" vars
       in (Consts.fmt "Lemma %s:  %s, %s.\nAdmitted." Consts.lfind_lemma var_forall conc)
     )
    else
    (
      let vars_all = List.fold_left (fun acc v -> acc ^ " " ^ v)  "" vars
      in (Consts.fmt "Lemma %s %s %s:%s.\nAdmitted." Consts.lfind_lemma vars_all (String.concat " " hyps) conc)
    )

let lfind_tac  : unit Proofview.tactic =
  Proofview.Goal.enter
  begin fun gl ->
    let is_running = Utils.get_env_var "is_lfind"
    in if String.equal is_running "true" then Tacticals.New.tclZEROMSG (Pp.str ("Recursive Lfind..Aborting"))
    else
      begin
        let curr_state_lemma = construct_state_as_lemma gl
        in print_endline curr_state_lemma;
        let p_ctxt, c_ctxt = construct_proof_context gl
        in Log.stats_log_file := p_ctxt.dir ^ Consts.log_file;
        Log.error_log_file := p_ctxt.dir ^ Consts.error_log_file;

        let example_file = Consts.fmt "%s/examples_%s.txt" p_ctxt.dir p_ctxt.fname
        in let coq_examples = Examples.get_examples example_file
        in let ml_examples = Examples.get_ml_examples coq_examples p_ctxt

        in let op = FileUtils.run_cmd "export is_lfind=true"
        in let abstraction = Abstract_NoDup.abstract
        in let generalized_terms, conjectures = abstraction p_ctxt c_ctxt

        (* create a lemma file to use with proverbot *)
        in let curr_state_lemma_file = Consts.fmt "%s/%s.v" p_ctxt.dir Consts.lfind_lemma
        in let content = Consts.fmt "%s\n Require Import %s.\n %s"
                         p_ctxt.declarations
                         p_ctxt.fname
                         curr_state_lemma
        in FileUtils.write_to_file curr_state_lemma_file content;

        (* get ml and coq version of the generalized examples *)
        let coq_examples, ml_examples = (ExampleUtils.evaluate_terms generalized_terms coq_examples ml_examples p_ctxt)
        in List.iter (fun c -> LogUtils.write_tbl_to_log c "COQE") coq_examples;
        List.iter (fun c -> LogUtils.write_tbl_to_log c "MLE") ml_examples;
        
        let valid_conjectures, invalid_conjectures = (Valid.split_as_true_and_false conjectures p_ctxt)
        in 
        List.iter (  
          fun c -> 
          print_endline c.conjecture_name;
          (* if (String.equal c.conjecture_name "conj9") then *)
          (Synthesize.synthesize p_ctxt ml_examples coq_examples c);
          (* else () *)
          ) 
          invalid_conjectures ;

        Stats.summarize !Stats.global_stat;

        Tacticals.New.tclZEROMSG (Pp.str ("Done.."))
      end
  end