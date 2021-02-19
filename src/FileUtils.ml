
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

let rec input_lines l ic : string list =
  match input_line ic with
  | line -> input_lines (line :: l) ic
  | exception End_of_file -> List.rev l

let run_cmd cmd =
  print_endline cmd;
  let inp = Unix.open_process_in cmd
  in let r = input_lines [] inp in
  close_in inp; r

let cp_dir src dst =
  let cmd = "cp -r " ^ src ^ " " ^ dst
  in let cmd_op = run_cmd cmd
  in ()