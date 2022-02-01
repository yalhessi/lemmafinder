open Lfindalgo

let check_path path =
  String.length (Utils.get_env_var path) > 1

let proverbot_path () =
  let is_path_set = check_path "PROVERBOT"
  in Alcotest.(check bool) "proverbot path set" true is_path_set

let myth_path () =
  let is_path_set = check_path "MYTH"
  in Alcotest.(check bool) "myth path set" true is_path_set

let astrewriter_path () =
  let is_path_set = check_path "REWRITE"
  in Alcotest.(check bool) "ast rewriter path set" true is_path_set

let coqofocaml_path () =
  let is_path_set = check_path "COQOFOCAML"
  in Alcotest.(check bool) "coq_of_ocaml path set" true is_path_set

let all = [
  ("test proverbot path"   ,        `Quick, proverbot_path);
  ("test myth path"        ,        `Quick, myth_path);
  ("test ast rewriter path",        `Quick, astrewriter_path);
  ("test coq_of_ocaml path",        `Quick, coqofocaml_path);
]