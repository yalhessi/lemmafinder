open LatticeUtils
open Consts

type synthesis_stat = {
    synthesis_term : string;
    enumerated_exprs : string list;
    valid_lemmas : (string * conjecture) list;
    provable_lemmas : (string * conjecture) list;
}

type generalization_stat = {
    conjecture : conjecture;
    is_valid : bool;
    is_provable : bool;
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

let get_synthesized_provable_lemmas stats=
    List.fold_left (fun acc g_stat -> 
                        acc + 
                        (List.fold_left (fun acc s_stat -> 
                                            acc + (List.length s_stat.provable_lemmas)
                                        ) 0 g_stat.synthesis_stats
                        )
                ) 0 stats

let summarize stats=
    let no_valid_gen_lemmas = List.length (List.filter (fun g -> g.is_valid) stats)
    in let total_synthesized_valid_lemmas = get_synthesized_valid_lemmas stats
    in let total_synthesized_provable_lemmas = get_synthesized_provable_lemmas stats
    in let summary =  (fmt "\n### SUMMARY ###\n"
    ^
    fmt "# Generalizations : %d\n" (List.length stats)
    ^
    fmt "#Valid lemmas from Generalization : %d\n" no_valid_gen_lemmas
    ^
    fmt "#Valid lemmas from Synthesis : %d\n" total_synthesized_valid_lemmas
    ^
    fmt "#Lemmas from Synthesis that can prove the original goal: %d\n" total_synthesized_provable_lemmas)

    in Log.write_to_log summary !Log.stats_log_file; ()

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
    fmt "is_provable (can help prove original goal): %b\n" (gen_stat.is_provable)
    ^
    fmt "Synthesis Stats : \n %s \n" (synthstats_to_string gen_stat.synthesis_stats)
