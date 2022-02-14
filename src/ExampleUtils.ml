exception Mismatch_Examples of string

let combine_examples (input_examples: ((string, string) Hashtbl.t) list)
                     (generalized_examples: (string, string list) Hashtbl.t)
                    : ((string, string) Hashtbl.t) list=
  let counter = ref (-1)                    
  in let combined_examples = List.fold_left (
                                fun acc tbl -> 
                                      let tbl_cpy = Hashtbl.copy tbl
                                      in let index = (Utils.next_val counter ())
                                      in Hashtbl.iter (fun k _ ->
                                                            let gen_examples = (Hashtbl.find generalized_examples k)
                                                            in (Hashtbl.add tbl_cpy k (List.nth gen_examples index));
                                                      ) generalized_examples;
                                      tbl_cpy::acc
                             ) [] input_examples
  in combined_examples

let evaluate_terms (generalized_terms : Sexp.t list list)
                   (coq_examples: (string, string) Hashtbl.t list)
                   (ml_examples: (string, string) Hashtbl.t list)
                   (p_ctxt: ProofContext.proof_context)
                  : ((string, string) Hashtbl.t list  * (string, string) Hashtbl.t list)=
  (* 
    Input: Set of generalized terms, coq and ml versions of input examples
    Output: Set of examples in coq and ml, including evaluations generalized of terms
  *)
  Log.debug (Consts.fmt "#Coq Input Examples %d\n" (List.length coq_examples));
  Log.debug (Consts.fmt "#ML Input Examples %d\n" (List.length ml_examples));
  Log.debug (Consts.fmt "#Generalzed terms %d\n" (List.length generalized_terms));
  
  let no_terms = List.length generalized_terms
  in let coq_term_examples, ml_term_example = List.fold_left (
                     fun (coq_acc, ml_acc) term -> 
                        let coq_term_output, ml_term_output = (Evaluate.evaluate_coq_expr term coq_examples p_ctxt p_ctxt.vars (Hashtbl.create 0) None)
                        in LogUtils.write_list_to_log coq_term_output ("Coq output of " ^ (Sexp.string_of_sexpr term));
                        LogUtils.write_list_to_log ml_term_output ("ML output of " ^ (Sexp.string_of_sexpr term));
                        let is_example_size_mismatch =  if (List.length ml_examples != List.length ml_term_output) then true else false
                        in if is_example_size_mismatch then raise @@ Mismatch_Examples "Mismatch between input examples and generalized variable output"
                        else
                        (
                          (Hashtbl.add coq_acc (Sexp.string_of_sexpr term) coq_term_output);
                          (Hashtbl.add ml_acc (Sexp.string_of_sexpr term) ml_term_output);
                          coq_acc,ml_acc
                        )
                    ) ((Hashtbl.create no_terms),(Hashtbl.create no_terms)) generalized_terms
  in let combined_coq_examples = combine_examples coq_examples coq_term_examples
  in let combined_ml_examples = combine_examples ml_examples ml_term_example
  in combined_coq_examples, combined_ml_examples