exception Invalid_Env of string

let contains s1 s2 =
  let re = Str.regexp_string s2 in
  try 
      ignore (Str.search_forward re s1 0); 
      true
  with Not_found -> false

let rec find_in_list (eq : 'a -> 'a -> bool) (x : 'a) (lst : 'a list) : 'a option =
  match lst with
  | [] -> None
  | h :: t -> if (eq x h) then Some h else (find_in_list eq x t)

let get_str_of_pp pp_expr : string =  Pp.string_of_ppcmds pp_expr

let get_econstr_str env sigma expr : string = (get_str_of_pp (Printer.pr_goal_concl_style_env env sigma expr))
  
let get_func_str_with_mod (env : Environ.env) (sigma : Evd.evar_map) (func : EConstr.t) : string = 
  try 
    let (name,_) = EConstr.destConst sigma func in
    "@" ^ (Names.Constant.modpath name |> Names.ModPath.to_string) ^ "." ^ (Names.Constant.label name |> Names.Label.to_string)
  with _ -> try 
    let ((ind,_),_) = EConstr.destInd sigma func in
    "@" ^ (Names.MutInd.modpath ind |> Names.ModPath.to_string) ^ "." ^ (Names.MutInd.label ind |> Names.Label.to_string)  
  with _ -> try 
    let (((construct,_),_),_) = EConstr.destConstruct sigma func in
    "@" ^ (Names.MutInd.modpath construct |> Names.ModPath.to_string) ^ "." ^ (Names.MutInd.label construct |> Names.Label.to_string) 
  with _ -> print_endline "In Utils.ml, missing potential function because we don't have full path"; ""
    (* raise (Failure ("Fail to get full function path (triggered in Utils.ml) : " ^ get_econstr_str env sigma func)) *)
  
let get_env_var env_var : string =
  let env = Unix.environment ()
  in Array.fold_left 
  (fun path p -> 
    let p_list = Array.of_list(String.split_on_char '=' p)
      in let var = (try (Array.get p_list 0) with Invalid_argument _ -> "")
      in let var_path = try (Array.get p_list 1) with Invalid_argument _ -> ""
      in if String.equal var env_var then var_path else path
   )"" env

let gen_rand_str length =
let gen() = match Random.int(26+26+10) with
    n when n < 26 -> int_of_char 'a' + n
  | n when n < 26 + 26 -> int_of_char 'A' + n - 26
  | n -> int_of_char '0' + n - 26 - 26 in
let gen _ = String.make 1 (char_of_int(gen())) in
String.concat "" (Array.to_list (Array.init length gen))
  
let env_setup () =
  let prover_path = get_env_var Consts.prover
  in
  if String.equal prover_path "" then raise (Invalid_Env "Prover path not set!")
  else Consts.prover_path := if prover_path.[(String.length prover_path) -1] = '/' 
                           then prover_path
                           else prover_path ^ "/";
  let lfind_path = get_env_var "LFIND"
  in if String.equal lfind_path "" then raise (Invalid_Env "LFIND SRC path not set!")
  else Consts.lfind_path := if lfind_path.[(String.length lfind_path) -1] = '/' then lfind_path else lfind_path ^ "/"

(* Copied from the original FileUtils.ml files *)
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
  Consts.commands := !Consts.commands ^ command ^ "\n\n";
  if !Consts.debug then print_endline (Consts.fmt "%s\n" command) else ();
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
  close_out oc

let get_var_type (var : string) (type_table : (string, Evd.econstr * Evd.econstr option * Names.variable option) Hashtbl.t) : Evd.econstr option =
  try 
  match (Hashtbl.find type_table var) with
  | (typ,_,_) -> Some typ
  with _ -> None

let remove_duplicates (eq : 'a -> 'a -> bool) (lst : 'a list) : 'a list =
  let rec aux accum = function
  | [] -> accum
  | h :: t -> 
    if (List.exists (eq h) accum) then (aux accum t) else (aux (h :: accum) t)
  in List.rev (aux [] lst)

let get_keys (tbl : ('a, 'b) Hashtbl.t) : 'a list = Hashtbl.fold (fun x _ accum -> accum @ [x]) tbl []

let remove_parentheses x =
  if Char.equal '(' (String.get x 0) 
  then 
    if Char.equal ')' (String.get x ((String.length x) - 1)) 
    then String.sub x 1 ((String.length x) - 2)
    else x
  else x 