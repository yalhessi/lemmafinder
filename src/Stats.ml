open LatticeUtils
open Consts

type synthesis_stat = {
    synthesis_term : string;
    enumerated_exprs : string list;
    valid_lemmas : (string * conjecture) list;
    original_valid_lemmas : (string * conjecture) list;
    provable_lemmas : (string * conjecture) list;
    prover_provable_lemmas : conjecture list;
}

type generalization_stat = {
    conjecture : conjecture;
    is_valid : bool;
    is_provable : bool;
    is_prover_provable: bool;
    synthesis_stats : synthesis_stat list;
}

let global_stat : generalization_stat list ref = ref []

let get_synthesized_valid_lemmas stats=
    List.fold_left (fun acc g_stat -> 
                            acc + 
                            (List.fold_left (fun acc s_stat -> 
                                                acc + (List.length s_stat.valid_lemmas)
                                            ) 0 g_stat.synthesis_stats
                            )
                   ) 0 stats

let probable_lemmas_to_string provable_lemmas =
    List.fold_left (fun acc (_, lemma) -> 
                        acc
                        ^
                        fmt "\t\t\t Lemma : %s\n" lemma.conjecture_str
                ) "" provable_lemmas

let lemmas_to_string lemmas =
    List.fold_left (fun acc lemma -> 
                        acc
                        ^
                        fmt "\t\t\t Lemma : %s\n" lemma.conjecture_str
                ) "" lemmas

let get_synthesized_prover_provable_lemmas stats=
    List.fold_left (fun (acc,len) g_stat -> 
                    let new_acc, l = 
                    (List.fold_left
                        (fun (acc_synth,len) s_stat -> 
                            let l = len + (List.length s_stat.prover_provable_lemmas)
                            in let c_str = lemmas_to_string s_stat.prover_provable_lemmas
                            in if (List.length s_stat.prover_provable_lemmas) > 0
                                then (acc_synth ^ "\n" ^ c_str, l)
                                else acc_synth, l
                        ) (acc, 0) g_stat.synthesis_stats
                    )
                    in new_acc, len + l
                ) ("",0) stats

let get_synthesized_provable_lemmas stats=
    List.fold_left (fun (acc,len) g_stat -> 
                    let new_acc, l = 
                    (List.fold_left 
                        (fun (acc_synth,len) s_stat -> 
                            let l = len + (List.length s_stat.provable_lemmas)
                            in let c_str = probable_lemmas_to_string s_stat.provable_lemmas
                            in if (List.length s_stat.provable_lemmas) > 0
                                then (acc_synth ^ "\n" ^ c_str, l)
                                else acc_synth, l
                        ) (acc, 0) g_stat.synthesis_stats
                    )
                    in new_acc, len + l
                ) ("",0) stats

let generalized_lemma_useful stats : string *int =
    List.fold_left (fun (acc,l) g -> 
                            if g.is_provable then
                            ((acc ^ "\n" ^ g.conjecture.conjecture_str), l+1)
                            else (acc,l)
                   ) ("", 0) stats

let generalized_lemma_useful_and_provable stats : string *int =
List.fold_left (fun (acc,l) g -> 
                        if g.is_prover_provable then
                        ((acc ^ "\n" ^ g.conjecture.conjecture_str), l+1)
                        else (acc,l)
                ) ("", 0) stats

let summarize stats curr_state_lemma =
    (* The last stat is the same as the stuck state, it does not provide any useful indicator *)
    let useful_stats = (List.rev stats)
    in 
    let no_valid_gen_lemmas = List.length (List.filter (fun g -> g.is_valid) (List.tl useful_stats))
    in let gen_useful_provable_lemmas, len_gen_useful_provable_lemmas = generalized_lemma_useful_and_provable (List.tl useful_stats)
    in let gen_provable_lemmas, len_gen_provable_lemmas = generalized_lemma_useful (List.tl useful_stats)
    in let total_synthesized_valid_lemmas = get_synthesized_valid_lemmas (List.tl useful_stats)
    in let str_provable_lemmas, total_synthesized_provable_lemmas = get_synthesized_provable_lemmas (List.tl useful_stats)
    in let str_prover_provable_lemmas, total_synth_prover_provable_lemmas =
    get_synthesized_prover_provable_lemmas (List.tl useful_stats)
    in let summary =  (fmt "\n### SUMMARY ###\n"
    ^
    fmt "Time to first category 1 (s): %d \n" (!Consts.time_to_category_1)
    ^
    fmt "Total Time: %d \n" (int_of_float(Unix.time ()) - !Consts.start_time)
    ^
    fmt "Total Lemmas: %d \n" !Consts.total_synth
    ^
    fmt "Filter Quickchick: %d \n" !Consts.is_false
    ^
    fmt "Filter duplicate: %d \n" !Consts.is_dup
    ^
    fmt "Filter trivial: %d \n" !Consts.trivial_count
    ^
    fmt "Filter is_version: %d \n" !Consts.is_version_count
    ^
    fmt "Stuck Proof State: %s\n"  (curr_state_lemma)
    ^
    fmt "# Generalizations : %d\n" (List.length (List.tl useful_stats))
    ^
    fmt "#Generalizations useful in proving original goal and provable by proverbot: %d\nLemmas\n%s\n" len_gen_useful_provable_lemmas gen_useful_provable_lemmas
    ^
    fmt "#Generalizations useful in proving original goal: %d\nLemmas\n%s\n" len_gen_provable_lemmas gen_provable_lemmas
    ^
    fmt "#Generalizations not disprovable : %d\n" no_valid_gen_lemmas
    ^
    fmt "#Synthesized Lemmas useful in proving original goal and provable by proverbot: %d\nLemmas\n%s" total_synth_prover_provable_lemmas str_prover_provable_lemmas
    ^
    fmt "#Synthesized Lemmas useful in proving original goal: %d\nLemmas\n%s" total_synthesized_provable_lemmas str_provable_lemmas)
    ^
    fmt "#Synthesized Lemmas not disprovable : %d\n" total_synthesized_valid_lemmas

    in Log.write_to_log summary !Log.stats_summary_file; ()

let valid_lemmas_to_string valid_lemmas =
    List.fold_left (fun acc (synthesized_expr, lemma) -> 
                            acc
                            ^
                            fmt "\t\t\t Myth Term : %s\n" synthesized_expr
                            ^
                            fmt "\t\t\t Lemma : %s\n" lemma.conjecture_str
                   ) "" valid_lemmas

let synthstat_to_string synth_stat =
    fmt "\t\t\n### Synthesis Stats ###\n"
    ^
    fmt "\t\t Synthesis Term : %s\n" synth_stat.synthesis_term
    ^
    fmt "\t\t # Myth Enumerated Terms : %d\n" (List.length synth_stat.enumerated_exprs)
    ^
    fmt "\t\t # Valid Synthesized Lemmas : %d\n" (List.length synth_stat.valid_lemmas)
    ^
    fmt "\t\t Valid Lemmas\n %s\n" (valid_lemmas_to_string synth_stat.valid_lemmas)
    ^
    fmt "\t\t # Lemmas useful to prove original goal : %d\n" (List.length synth_stat.provable_lemmas)
    ^
    fmt "\t\t Lemmas that can prove the original goal \n %s\n" (valid_lemmas_to_string synth_stat.provable_lemmas)
    ^
    fmt "------------------------------------------------------------------------\n"


let synthstats_to_string synthesis_stats =
    List.fold_left (fun acc synth_stat -> acc ^ (synthstat_to_string synth_stat)) "" synthesis_stats

let genstat_to_string gen_stat =
    fmt "\n### Generalization Stat ###\n"
    ^
    fmt "Generalized Conjecture : %s\n" gen_stat.conjecture.conjecture_str
    ^
    fmt "is_valid : %b\n" (gen_stat.is_valid)
    ^ 
    fmt "is_prover_provable (be proven by proverbot): %b\n" (gen_stat.is_prover_provable)
    ^ 
    fmt "is_provable (can help prove original goal): %b\n" (gen_stat.is_provable)
    ^
    fmt "Synthesis Stats : \n %s \n" (synthstats_to_string gen_stat.synthesis_stats)
