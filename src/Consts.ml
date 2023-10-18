(* From original algorithm, commented to out un-used *)

let lfind_declare_module = "Load LFindLoad."

(* let synthesis_op = "lfind_output" *)
(* let type_decl = "Type" *)
(* let debug_log_file = "/lfind_debug_log.txt"
let log_file = "/lfind_log.txt"
let summary_log_file = "/lfind_summary_log.txt"
let error_log_file = "/error_lfind_log.txt" *)

(* changed to 15 *)
let synthesizer_timeout = "15"
let coq_printing_depth = "Set Printing Depth 1000."

let fmt = Printf.sprintf

let lfind_lemma = "lfind_state"
let quickchick_import = "From QuickChick Require Import QuickChick."
let string_scope = "Open Scope string_scope.\n"
let extract_print = "Extract Constant print => \"Extract.print\".\n"
let vernac_success = "Success."
let def_qc_num_examples = "Extract Constant defNumTests => \"50\"."

let prover = "PROVERBOT"
(* let synthesizer = ref "" *)
let prover_path = ref ""
(* let synthesizer_path = ref "" *)
let coq_synthesizer_path = "coq_synth"
let lfind_path = ref ""
let synth_batch_size = 6

(* let time_to_category_1 = ref 0

let logged_time_to_cat_1 = ref false

let trivial_count = ref 0

let is_version_count = ref 0

let total_synth = ref 0

let is_false = ref 0

let is_dup = ref 0

let lfind_lemma_content = ref "" *)

let start_time = ref 0
let clean_up = ref true
let debug = ref true
let progress = ref ""
let commands = ref ""