open Constr
open Context
open Proofview.Notations
open Sexp
open ProofContext
open Loadpath
open Loc
open Names
open LatticeUtils

let lfind_tac  : unit Proofview.tactic =
  Proofview.Goal.enter
  begin fun gl ->
    let is_running = Utils.get_env_var "is_lfind"
    in if String.equal is_running "true" then Tacticals.New.tclZEROMSG (Pp.str ("Recursive Lfind..Aborting"))
    else
      begin
        let p_ctxt, c_ctxt = construct_proof_context gl
        in Log.stats_log_file := p_ctxt.dir ^ Consts.log_file;
        Log.error_log_file := p_ctxt.dir ^ Consts.error_log_file;

        let example_file = Consts.fmt "%s/examples_%s.txt" p_ctxt.dir p_ctxt.fname
        in let coq_examples = Examples.get_examples example_file
        in let ml_examples = Examples.get_ml_examples coq_examples p_ctxt

        in let op = FileUtils.run_cmd "export is_lfind=true"
        in let abstraction = Abstract_NoDup.abstract
        in let generalized_terms, conjectures = abstraction p_ctxt c_ctxt

        (* get ml and coq version of the generalized examples *)
        in let coq_examples, ml_examples = (ExampleUtils.evaluate_terms generalized_terms coq_examples ml_examples p_ctxt)
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