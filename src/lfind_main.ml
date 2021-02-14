open Constr
open Context
open Proofview.Notations
open Sexp
open ProofContext
exception HammerError of string

(* let warning = CWarnings.create ~name:"name" ~category:"category"
                            (fun _ -> Pp.strbrk "Synthesizing helper lemma for the above goal") *)
let msg_in_tactic str : unit Proofview.tactic =
  Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
      Feedback.msg_warning (Pp.str str)))

let lfind_tac : unit Proofview.tactic =
  Proofview.Goal.enter 
  begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let goal = Proofview.Goal.concl gl in
    let hyps = Proofview.Goal.hyps gl in
    let c_ctxt = {env = env; sigma = sigma}
    in let p_ctxt = {hypotheses = []; goal = (Utils.get_expr_str env sigma goal); functions = []; samples = []}
    (* in Abstract_WPositions.abstract p_ctxt c_ctxt; *)
    in let abstraction = Abstract_NoDup.abstract
    in  abstraction p_ctxt c_ctxt;
     (* print_endline (string_of_goal gl); *)
     (* Feedback.msg_notice(string_of_goal gl); *)
    (* 
    let typ = Utils.get_type_of_exp env sigma (Utils.str_to_constr "n")
    in Feedback.msg_notice (Printer.pr_econstr_env env sigma typ);
     *)
    (* Feedback.msg_notice (Pp.str(string_of_sexpr_indent se)); *)
    (* let _ = warning () in
     Tacticals.New.tclIDTAC *)
     msg_in_tactic "Synthesizing helper lemmas" >>= fun () ->
     Tacticals.New.tclIDTAC
  end