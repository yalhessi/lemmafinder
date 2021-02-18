open LatticeUtils
open ProofContext

let remove_file fname : unit = 
  if Sys.file_exists fname then (Sys.remove fname) else ()

let generate_lfind_file p_ctxt conjecture count : string =
  let lfind_file = p_ctxt.dir ^ "/lfind" ^ count ^ ".v"
  in remove_file lfind_file;
  let content = "Require Import " ^ p_ctxt.fname ^ ".\n" 
                ^ "Lemma " ^ conjecture ^ ".\n"
                ^ "Admitted.\n"
  in let oc = open_out lfind_file in
  Printf.fprintf oc "%s" content;
  close_out oc;
  lfind_file

let check_provable conjecture p_ctxt count : bool =
  let lfind_file = generate_lfind_file p_ctxt conjecture.conjecture_str (string_of_int count)
  in Proverbot.run p_ctxt.dir (string_of_int count) conjecture.conjecture_name

let split_as_provable_non_provable conjectures p_ctxt : conjecture list * conjecture list =
  Proverbot.remove_current_search p_ctxt.dir;
  let counter = ref 0
  in List.fold_left (fun (true_conj, false_conj) c ->
                                    let is_provable = check_provable c p_ctxt (Utils.next_val counter ())
                                    in if is_provable 
                                        then (c::true_conj, false_conj) 
                                        else (true_conj, c::false_conj)
                    ) ([], []) conjectures