open OUnit2
open Lfindalgo

(* From the lfindalgo, uses modules:
   - Utils
   - Consts *)

(* To test that the environment is set up properly *)
let test_lfind_path = "lfind path set" >:: (fun _ -> assert_bool "LFind path is not set." (not (String.equal (Utils.get_env_var "LFIND") "")))
let test_prover_path = "prover path set" >:: (fun _ -> assert_bool "Prover path is not set." (not (String.equal (Utils.get_env_var Consts.prover)"")))

(* Lists of tests to run within a test object *)
let tests = "toy test suite" >::: [
  test_lfind_path;
  test_prover_path;
  GeneralizationTest.test();
  ConjectureGenerationTest.test();
  (* EndtoEnd.test (); *)
]

(* Runs the tests *)
let _ = run_test_tt_main tests