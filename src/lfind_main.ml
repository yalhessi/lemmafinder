open Constr
open Context
open Proofview.Notations
open Sexp
open ProofContext
open Loadpath
open Loc
open Names

let msg_in_tactic str : unit Proofview.tactic =
  Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
      Feedback.msg_warning (Pp.str str)))

let lfind_tac  : unit Proofview.tactic =
  Proofview.Goal.enter
  begin fun gl ->
    let p_ctxt, c_ctxt = construct_proof_context gl
    in Log.stats_log_file := p_ctxt.dir ^ Consts.log_file;
    Log.error_log_file := p_ctxt.dir ^ Consts.error_log_file;
    let abstraction = Abstract_NoDup.abstract
    in let conjectures = abstraction p_ctxt c_ctxt
    (* in let provable_conjectures, non_provable_conjectures = (Provable.split_as_provable_non_provable conjectures p_ctxt)
    in let provable_conjectures_str = LatticeUtils.conjs_to_string provable_conjectures
    in let generalization_output_str = Printf.sprintf ("Generalization found %d provable lemmas out of %d lemmas\n %s") (List.length provable_conjectures) (List.length conjectures) provable_conjectures_str
    in Feedback.msg_notice(Pp.str(generalization_output_str)); *)

    in let valid_conjectures, invalid_conjectures = (Valid.split_as_true_and_false conjectures p_ctxt)
    in let valid_conjectures_str = LatticeUtils.conjs_to_string valid_conjectures
    in let generalization_output_str = Printf.sprintf ("Generalization found %d valid lemmas out of %d lemmas\n %s") (List.length valid_conjectures) (List.length conjectures) valid_conjectures_str
    in Feedback.msg_notice(Pp.str(generalization_output_str));

    List.iter (Synthesize.synthesize p_ctxt) invalid_conjectures ;
    Stats.summarize !Stats.global_stat;

    Tacticals.New.tclZEROMSG (Pp.str ("Done.."))
  end