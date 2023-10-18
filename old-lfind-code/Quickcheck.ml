open FileUtils

let quickcheck fname namespace dir =
  let cmd = Consts.fmt "coqc -R %s %s %s" dir namespace fname
  in run_cmd cmd

let get_counter_example (op: string list) : string list = 
  (* assumes a counter example is returned *)
  let cgs, _ = List.fold_left (fun (acc, is_acc) l -> 
    if  Utils.contains l ".native" then acc, true 
    else
    (
      if Utils.contains l "Failed" then acc, false
      else (
            if is_acc then (List.append acc [l]), is_acc
            else acc, is_acc
          )
    )
) ([],false) op
in cgs


let output_code (op: string list)
                : bool * string list =
  let last_line = try List.hd (List.rev op)
                  with _ -> Log.write_to_log (String.concat "\n" op) !Log.error_log_file; ""
  in Log.debug (Consts.fmt "last line is : %s" last_line);
  (* This checks all of the operation output (incase last line is empty -- can optimize, simple fix right now) *)
  let valid = List.fold_left (fun acc l -> acc || (Utils.contains l "Passed") ) false op in
  let counterexample = List.fold_left (fun acc l -> acc || (Utils.contains l "Failed") ) false op in
  if valid then true, []
  else if counterexample then false, (get_counter_example op)
  else
    (
      print_endline "QuickChick did not run successfully...";
      Log.write_to_log (String.concat "\n" op) !Log.error_log_file;
      exit(0);
    )
  

let run (fname: string) (namespace: string) (dir: string)
        : bool * string list =
  if !Opts.enable_quickchick 
    then 
    (let results = quickcheck fname namespace dir in
      output_code results)
  else
    (false, [])
  

let remove_files dir =
  let cmd = "rm -rf " ^ dir ^ "/lfindconj*"
  in let cmd_op = run_cmd cmd
  in ()