open OUnit2
open Lfindalgo

(* From the lfindalgo, uses modules:
   - Utils
   - FileUtils
   - Consts *)

(* Helper function to get the index of a line *)
let get_index str list =
  let rec iterate index = function
  | [] -> -1
  | hd :: tl -> if Utils.contains hd str then index else iterate (index + 1) tl
  in iterate 0 list

(* Helper function to get the number of lemmas in each category (from the summary text file) *)
let get_category_counts list =
  let c1_line = get_index "Provable and Useful in Completing Stuck Goal (Category 1)" list in
  let c2_line = get_index "Useful in Completing Stuck Goal (Category 2)" list in
  let c3_line = get_index "Valid Lemmas (Category 3)" list in
  if c1_line < 0 or c2_line < 0 or c3_line < 0 then -1,-1,-1
  else (c2_line - c1_line -2), (c3_line - c2_line -2),((List.length list) - c3_line -3)

(* Helper function to parse summary file content *)
let parse_results results = 
  let expected_lemmas = 52 in
  let expected_1_lemmas = 1 in
  let expected_2_lemmas = 8 in
  let expected_3_lemmas = 44 in
  let rec iterate = function
  | [] -> -1
  | line :: remaining ->
    if Utils.contains line "#Synthesized Lemmas not disprovable" 
      then let elem = String.split_on_char ':' line in int_of_string (Utils.strip (List.nth elem 1))
      else iterate remaining
  in let syn_lemmas = iterate results in
  let c1_lemmas, c2_lemmas, c3_lemmas = get_category_counts results in
  if (syn_lemmas = expected_lemmas & c1_lemmas = expected_1_lemmas & 
    c2_lemmas = expected_2_lemmas & c3_lemmas = expected_3_lemmas)
  then (true, "success")
  else (false, 
  "Expected Category 1: " ^ string_of_int expected_1_lemmas ^ " -> Actual: " ^ string_of_int c1_lemmas ^
  "\nExpected Category 2: " ^ string_of_int expected_2_lemmas ^ " -> Actual: " ^ string_of_int c2_lemmas ^
  "\nExpected Category 3: " ^ string_of_int expected_3_lemmas ^ " -> Actual: " ^ string_of_int c3_lemmas)

(* Helper function to generate the results for the unit test *)
let test_helper () =
  let lfind_folder = Utils.get_env_var "LFIND" in
  if String.equal lfind_folder "" then (false, "LFind path not set") 
  else if String.equal (Utils.get_env_var Consts.prover) "" then (false, "Prover path not set")
  else 
    let test_folder = lfind_folder ^ "/unit-tests/tests/test-revappend" in
    let lfind_test_folder = lfind_folder ^ "/unit-tests/tests/_lfind_test-revappend" in
    let result_file = lfind_test_folder ^ "/lfind_summary_log.txt" in
    let cmd = "cd " ^ test_folder ^ " && make" in
    let _ = FileUtils.run_cmd cmd in
    let file_info = FileUtils.read_file result_file in
    let result = if List.length file_info = 0 then (false, "End to end run failed to yield lfind_summary_log file.")
    else parse_results (List.rev file_info) in
    let rm_cmd = "rm -r " ^ lfind_test_folder in let _ = FileUtils.run_cmd rm_cmd in result

(* Driver function *)
let test () =
  match test_helper () with
  | (success,msg) -> "end to end test" >:: (fun _ -> assert_bool msg success)