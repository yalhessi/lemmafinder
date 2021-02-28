open FileUtils

let quickcheck prelude fname =
  (* TODO: fix this hardcoding for namespace, we can get this when getting the path *)
  let cmd = "coqc -R . test " ^ prelude ^ fname
  in run_cmd cmd

let output_code op =
  let last_line = List.hd (List.rev op)
  in let is_contains = Utils.contains last_line "Passed"
  in is_contains

let run prelude conjecture_name =
  let fname = "/lfind" ^ conjecture_name ^".v "
  in (output_code (quickcheck prelude fname))