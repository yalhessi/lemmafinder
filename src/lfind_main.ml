open Constr
open Context
open Proofview.Notations
open Sexp
open ProofContext
open Loadpath
open Loc
open Names

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

        let op = FileUtils.run_cmd "export is_lfind=true"
        in let abstraction = Abstract_NoDup.abstract
        in let conjectures = abstraction p_ctxt c_ctxt

        in let valid_conjectures, invalid_conjectures = (Valid.split_as_true_and_false conjectures p_ctxt)
        in List.iter (Synthesize.synthesize p_ctxt) invalid_conjectures ;

        Stats.summarize !Stats.global_stat;

        Tacticals.New.tclZEROMSG (Pp.str ("Done.."))
      end
  end