open FileUtils

let quickcheck fname namespace =
  let cmd = Consts.fmt "coqc -R . %s %s" namespace fname
  in run_cmd cmd

let output_code op =
  let last_line = try List.hd (List.rev op) with _ -> Log.write_to_log (String.concat "\n" op) !Log.error_log_file; ""
  in let is_contains = Utils.contains last_line "Passed"
  in is_contains

let run fname namespace =
  (output_code (quickcheck fname namespace))