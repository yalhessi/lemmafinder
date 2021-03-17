let stats_log_file : string ref = ref ""
let error_log_file : string ref = ref ""

let write_to_log content log_file =
  let oc = open_out_gen [Open_append; Open_creat] 0o666 log_file in
  Printf.fprintf oc "%s\n" content;
  close_out oc; ()