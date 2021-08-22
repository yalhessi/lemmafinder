let stats_log_file : string ref = ref ""
let error_log_file : string ref = ref ""
let stats_summary_file : string ref = ref ""
let log_chan = ref stderr
let debug_file : string ref = ref ""

type level = Debug | Error | Info
  let level_str = function Debug -> "( debug )"
                         | Error -> "< ERROR >"
                         | Info  -> "(  info )"

let do_log level lstr =
  begin
    try 
      let oc = open_out_gen [Open_append; Open_creat] 0o666 !debug_file
      in Printf.fprintf oc
        "%s  %s\n"
        (level_str level)
        (lstr);
        close_out oc;
    with
    _ -> ()
  end

let info lstr = do_log Info lstr
let debug lstr = do_log Debug lstr
let error lstr = do_log Error lstr

let enable_debug fname = 
    (* log_chan := open_out_gen [Open_append; Open_creat] 0o666 fname; *)
    debug_file := fname;
    ()

let write_to_log content log_file =
  let oc = open_out_gen [Open_append; Open_creat] 0o666 log_file in
  Printf.fprintf oc "%s\n" content;
  close_out oc; ()