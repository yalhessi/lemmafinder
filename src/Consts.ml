let lfind_declare_module = "Declare ML Module \"lfind_plugin\"."

let synthesis_op = "lfind_output"

let type_decl = "Type"

let debug_log_file = "/lfind_debug_log.txt"

let log_file = "/lfind_log.txt"

let summary_log_file = "/lfind_summary_log.txt"

let error_log_file = "/error_lfind_log.txt"

let myth_timeout = "12"

let coq_printing_depth = "Set Printing Depth 1000."

let fmt = Printf.sprintf

let extract_nat = "Extract Inductive nat => nat [ \"(O)\" \"S\" ]."

let extract_list = "Extract Inductive list => list [ \"Nil\" \"Cons\" ]."

let lfind_lemma = "lfind_state"

let quickchick_import = "From QuickChick Require Import QuickChick."

let string_scope = "Open Scope string_scope.\n"

let extract_print = "Extract Constant print => \"Extract.print\".\n"

let require_extraction = "\nRequire Coq.extraction.Extraction.\nExtraction Language OCaml.\n"

let vernac_success = "Success."

let extraction_import = "Require Import Extraction."

let def_qc_num_examples = "Extract Constant defNumTests => \"50\"."