let generate_completion_file (context : LFContext.t) : unit =
  let eval_file = context.lfind_dir ^ "/lfind_eval_for_completion.v" in
  let curr_state = BlackBox.pp_goal_for_prover context in
  let content = String.concat "\n" 
  [LFUtils.coq_file_intro context; curr_state; "Admitted."] in
  Utils.write_to_file eval_file content

let create_provable_lemma_eval_for_conj (context : LFContext.t) (conj : Conjecture.t) : string =
  let eval_file = context.lfind_dir ^ (Consts.fmt "/lfind_proverbot_eval_%s.v" conj.label) in
  let file_intro = LFUtils.coq_file_intro context in
  let content = String.concat "\n" 
  [file_intro; (Conjecture.get_pretty_print context conj); "Admitted."] in
  Utils.write_to_file eval_file content;
  eval_file 

let proverbot_search (prelude : string) (file : string) (conjecture_name : string) (axioms : string ): string =
  Random.self_init ();
  let proof_timeout = 20 in
  let cmd_timeout = 40 in
  let rnd_str = Utils.gen_rand_str 6 in
  let python = "python3 " in
  let script = !Consts.prover_path ^ "src/search_file.py " in
  let weights_file  = !Consts.prover_path ^ "data/polyarg-weights.dat " in
  let search_report = Consts.fmt "search-report-%s-%s" conjecture_name rnd_str in
  let cmd = Consts.fmt 
  "timeout %d python3 %s --prelude=%s --weightsfile=%s %s %s --no-generate-report --max-proof-time=%d -o %s/%s" 
  cmd_timeout script prelude weights_file file axioms proof_timeout prelude search_report in
  print_endline "proverbot command:";
  print_endline cmd;
  let run_op = Utils.run_cmd cmd in search_report

let interpret_proverbot (prelude : string) (conjecture_name : string) (report_name : string) : bool =
  let cmd = "cat " ^ prelude ^"/" ^ report_name ^ "/*-proofs.txt | grep SUCCESS | grep " ^ conjecture_name ^ " -c" in
  print_endline "parsing command:";
  print_endline cmd;
  let cmd_op = Utils.run_cmd cmd in
  try
    match List.hd cmd_op with
    | "1" -> print_endline "true\n"; true
    | _ -> print_endline "false\n"; false
  with _ -> print_endline "false\n"; false

let check_conjecture_with_proverbot (context : LFContext.t) (conj : Conjecture.t) : bool =
  let prelude = context.lfind_dir in
  let file = create_provable_lemma_eval_for_conj context conj in
  let proof_name = conj.label in
  let report_folder = proverbot_search prelude file proof_name "" in
  interpret_proverbot prelude proof_name report_folder

let generate_axiom_file (context : LFContext.t) (conj : Conjecture.t) : string =
  let axiom_file = context.lfind_dir ^ (Consts.fmt "/lfind_axiom_%s.txt" conj.label) in
  let content = (Conjecture.get_pretty_print context conj) ^ "\n" in
  Utils.write_to_file axiom_file content; axiom_file 

let check_proof_state_with_conj (context : LFContext.t) (conj : Conjecture.t) : bool =
  let prelude = context.lfind_dir in
  let file = context.lfind_dir ^ "/lfind_eval_for_completion.v" in
  let proof_name = "current_goal" in
  let axioms = generate_axiom_file context conj in
  let report_folder = proverbot_search prelude file proof_name ("--add-axioms="^axioms) in
  interpret_proverbot prelude proof_name report_folder

let rank (context : LFContext.t) (conjectures : Conjecture.t list) : Conjecture.t list * Conjecture.t list * Conjecture.t list =
  generate_completion_file context;
  let (r_one,r_two,r_three) = List.fold_left
  (
    fun (one,two,three) conj ->
      let is_provable = check_conjecture_with_proverbot context conj in 
      let proves_theorem = check_proof_state_with_conj context conj in 
      let conj_to_add = { conj with provable = is_provable; } in
      match (is_provable,proves_theorem) with
      | (true,true) -> (conj_to_add::one,two,three)
      | (false,true) -> (one,conj_to_add::two,three)
      | _ -> (one,two,conj_to_add::three)
  ) ([],[],[]) conjectures in  
  (List.rev r_one,List.rev r_two, List.rev r_three)