open Constr
open Context
open Proofview.Notations
open Sexp
open ProofContext
open Loadpath
open Loc

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
    let hyps_strl = Utils.get_hyps_strl hyps env sigma in
    let c_ctxt = {env = env; sigma = sigma}
    in let paths = Loadpath.get_load_paths ()
    (* in List.iter (fun path -> print_endline (Utils.get_str_of_pp (Loadpath.pp  (path)))) paths; *)
    (* let dir = List.hd (List.rev (String.split_on_char ' ' (Utils.get_str_of_pp (Loadpath.pp (List.hd paths))))) *)
    in let dir = LatticeUtils.get_dir paths
    in let parent_dir, curr_dir = FileUtils.get_parent_curr_dir dir in
    let lfind_dir = parent_dir ^ "_lfind_" ^ curr_dir in
    FileUtils.cp_dir dir (lfind_dir);
    let full_context = Utils.get_str_of_pp (Prettyp.print_full_context env sigma)
    in let f_name = ProofContext.get_fname full_context
    in let p_ctxt = {
                     hypotheses = hyps_strl; 
                     goal = (Utils.get_expr_str env sigma goal); 
                     functions = []; 
                     samples = [];
                     dir = lfind_dir;
                     full_context = full_context;
                     fname = f_name;
                    }
    (* copy the folder for lfind purposes  -- this call is blocking *)
    
    (* in Abstract_WPositions.abstract p_ctxt c_ctxt; *)
    in let abstraction = Abstract_NoDup.abstract
    in let conjectures = abstraction p_ctxt c_ctxt
    in let provable_conjectures, non_provable_conjectures = (Provable.split_as_provable_non_provable conjectures p_ctxt)
    in let provable_conjectures_str = LatticeUtils.conjs_to_string provable_conjectures
    in let generalization_output_str = Printf.sprintf ("Generalization found %d provable lemmas out of %d lemmas\n %s") (List.length provable_conjectures) (List.length conjectures) provable_conjectures_str
    in Feedback.msg_notice(Pp.str(generalization_output_str));

    let valid_conjectures, non_valid_conjectures = (Valid.split_as_true_and_false conjectures p_ctxt)
    in let valid_conjectures_str = LatticeUtils.conjs_to_string valid_conjectures
    in let generalization_output_str = Printf.sprintf ("Generalization found %d valid lemmas out of %d lemmas\n %s") (List.length valid_conjectures) (List.length conjectures) valid_conjectures_str
    in Feedback.msg_notice(Pp.str(generalization_output_str));

    msg_in_tactic "Done.." >>= fun () ->
    Tacticals.New.tclIDTAC
  end