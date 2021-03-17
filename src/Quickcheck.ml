open FileUtils

let quickcheck prelude fname namespace =
  (* TODO: fix this hardcoding for namespace, we can get this when getting the path *)
  let cmd = Consts.fmt "coqc -R . %s %s%s" namespace prelude fname
  in run_cmd cmd

let output_code op =
  let last_line = try List.hd (List.rev op) with _ -> Log.write_to_log (String.concat "\n" op) !Log.error_log_file; ""
  in let is_contains = Utils.contains last_line "Passed"
  in is_contains

let run prelude conjecture_name namespace =
  let fname = "/lfind" ^ conjecture_name ^".v "
  in (output_code (quickcheck prelude fname namespace))