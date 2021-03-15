open Stdlib
open FileUtils

let scrape_data prelude proverbot fname =
  let python = "python3 " 
  in let script = proverbot ^ "src/scrape.py "
  in let cmd = python ^ script ^ "--prelude="^ prelude ^ fname ^" -P"
  in let run_op = run_cmd cmd
  in ()

let search prelude proverbot fname =
  let python = "python3 " 
  in let script = proverbot ^ "src/search_file.py "
  in let weigths_file  = " --weightsfile=" ^ proverbot ^"data/polyarg-weights.dat "
  in let cmd = python ^ script ^ "--prelude="^ prelude ^ weigths_file ^  fname ^ " -P"
               ^ " -o " ^ prelude ^ "/search-report"
  in let run_op = run_cmd cmd
  in List.iter (Printf.printf "Line from stdout: %s\n") run_op

let output_code prelude conjecture_name : bool =
  let cmd = "cat " ^ prelude ^"/search-report/*-proofs.txt | grep SUCCESS | grep " ^ conjecture_name ^ ": -c"
  in let cmd_op = run_cmd cmd
  in if cmd_op = [] 
      then false 
      else
      (match List.hd cmd_op with
      | "0" -> false
      | "1" -> true
      | _ -> false)

let remove_current_search prelude =
  let cmd = "rm -rf " ^ prelude ^ "/search-report"
  in let cmd_op = run_cmd cmd
  in ()

let run prelude conjecture_name =
  let prover_bot_path = Utils.get_env_var "PROVERBOT" 
  in let fname = " lfind" ^ conjecture_name ^".v "
  in scrape_data prelude prover_bot_path fname;
  search prelude prover_bot_path fname;
  let code = (output_code prelude conjecture_name)
  in Printf.printf "Code for conjecture %s is %b\n" conjecture_name code;
  code