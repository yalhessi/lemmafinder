let get_parent_curr_dir dir = 
  let rec aux acc curr dir_split = 
    match dir_split with
    | [] -> acc, curr
    | x :: [] -> acc, x 
    | x :: xs -> let new_acc, new_curr = (aux (acc ^ x ^ "/") curr xs)
                  in new_acc, new_curr
  in
  aux "" "" (String.split_on_char '/' dir)

let remove_file fname : unit = 
  if Sys.file_exists fname then (Sys.remove fname) else ()

let run_cmd command = 
  Log.debug(Consts.fmt "%s\n" command);
  let channel = Unix.open_process_in command in
  let result = ref ([] : string list) in
  let rec process_aux () =
    let tmp = input_line channel in
    result := tmp :: !result;
    process_aux() in 
  try process_aux ()
  (* The stat is the exit status of the process *)
  with End_of_file -> let stat = close_in channel in 
  List.rev !result

let rm_dir dir =
  let cmd = "rm -rf " ^ dir
  in let cmd_op = run_cmd cmd
  in ()

let cp_dir src dst =
  rm_dir dst;
  let cmd = "cp -r " ^ src ^ " " ^ dst
  in let cmd_op = run_cmd cmd
  in ()

let read_file filename =
  (* 
    Input: string - file name
    Ouput: list string - file content in reverse order
  *)
  let lines = ref [] in
  try
    let chan = open_in filename in
    try
      while true; do
        lines := input_line chan :: !lines
      done; !lines
    with End_of_file ->
      close_in chan;
      !lines
  with _ -> !lines
  
let write_to_file fname content =
  remove_file fname;
  let oc = open_out_gen [Open_wronly; Open_creat; Open_trunc; Open_text] 0o777 fname
  in Printf.fprintf oc "%s" content;
  close_out oc;