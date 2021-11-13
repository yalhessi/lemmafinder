import argparse
import os
import csv
from posixpath import dirname, split
from re import S, search, sub
import sys
import coq_serapy
import subprocess
import shutil
import operator, functools



class LogDetails(object):
    def __init__(self) -> None:
        super().__init__()
        self.log_dir = ""
        self.no_gen_provable = 0 
        self.no_synth_provable = 0
        self.provable_lemmas = []
        self.total_gen = 0
        self.total_synth = 0
        self.is_stuck_provable = False
        self.no_gen_useful_stuck_provable = 0
        self.no_syn_useful_stuck_provable = 0
        self.useful_stuck_provable_lemmas = []
        self.valid_lemmas = []
        self.matches_human = False
        self.is_stronger_than_human = False
        self.is_weaker_than_human = False
        self.matched_lemma = ""
        self.matched_lemma_loc = 0
        self.stronger_lemma = ""
        self.stronger_lemma_loc = 0
        self.weaker_lemma = ""
        self.weaker_lemma_loc = 0
        self.helper_name = "" 
        self.helper_lemma = ""
        self.is_auto_provable = False
        self.top_answer = ""

    def row(self):
        return [self.log_dir,self.is_stuck_provable,self.no_gen_provable,self.no_synth_provable, self.no_gen_useful_stuck_provable,self.no_syn_useful_stuck_provable,len(self.valid_lemmas), self.matches_human, self.matched_lemma,self.matched_lemma_loc,self.stronger_lemma,self.stronger_lemma_loc,self.weaker_lemma, self.weaker_lemma_loc, self.helper_name, self.helper_lemma, self.is_auto_provable, self.top_answer, self.total_synth, self.total_gen]


def get_lemmas(benchmark_file):
    import json
    with open(benchmark_file, 'r') as j:
     all_lemmas = json.loads(j.read())    
    return all_lemmas

def parse_arguments():
    parser = argparse.ArgumentParser(
        description=
        "Rank and Generate CSV")
    parser.add_argument('--lfind_op', default="test")
    parser.add_argument('--log_dir', default=".")
    parser.add_argument('--trivial_ld', default=".")
    parser.add_argument('--trivial', default=False)
    return parser.parse_args(), parser

def write_missing_lemmasto_csv(missing_lemmas, log_dir):
    csv_file = os.path.join(log_dir, "missing.csv")
    column_name = ["Missing", "Reason"]
    with open(csv_file, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(column_name)
        for key, value in missing_lemmas.items():
            writer.writerow([key, value])     

def sort_logs_by_goal_no(log):
    return os.path.basename(log.log_dir).split("_")[4].replace("goal","")

def write_log_objs(csv_file, log_objs):
    column_names = ["log_dir",
"is_stuck_provable",
"no_gen_provable",
"no_synth_provable",
"no_gen_useful_stuck_provable",
"no_syn_useful_stuck_provable",
"len(valid_lemmas)",
"matches_human",
"matched_lemma",
"matched_lemma_loc",
"stronger_lemma",
"stronger_lemma_loc",
"weaker_lemma",
"weaker_lemma_loc",
"helper_name",
"helper_lemm",
"is_provable",
"synth/gen",
"total_synth",
"total_gen"]
    with open(csv_file, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(column_names)
        s = sorted(log_objs, key=sort_logs_by_goal_no)
        for log_obj in s:
            writer.writerow(log_obj.row())

class MissingLogException(Exception):
    def __init__(self, message):
        super().__init__(message)

def get_helper_lemma(prelude):
    benchmark_file = os.path.join(prelude, "lemmafinder_bench.txt")
    benchmark_lemmas = get_lemmas(benchmark_file)
    orig_lemma_name = os.path.basename(prelude)
    lemma_filename = ""
    for f in os.listdir(prelude):
         if f.endswith(".txt") and "examples" in f:
             lemma_filename = f.replace(".txt", "").replace("examples_", "")
    theorem_name = ""
    alternate_theorem_name = ""
    for k in benchmark_lemmas:
        locs = benchmark_lemmas[k]
        for l in locs:
            comb_name = l[0].replace("'","") + "_" + str(l[1])+ "_"+l[2]
            split_name = orig_lemma_name.split(lemma_filename + "_")
            if split_name[1] == comb_name:
                theorem_name = l[2].replace("'","")
                alternate_theorem_name = os.path.basename(k).split(".")[0] + "_" + theorem_name
            elif len(split_name) > 2 and split_name[2] == comb_name:
                theorem_name = l[2].replace("'","")
                alternate_theorem_name = os.path.basename(k).split(".")[0] + "_" + theorem_name
    return theorem_name, alternate_theorem_name

def is_lemma_version_of_theorem(lemma, prelude, all_lemmas, imports):
    lemma = lemma + "."
    benchmark_file = os.path.join(prelude, "lemmafinder_bench.txt")
    benchmark_lemmas = get_lemmas(benchmark_file)
    orig_lemma_name = os.path.basename(prelude)
    lemma_filename = ""
    for f in os.listdir(prelude):
         if f.endswith(".txt") and "examples" in f:
             lemma_filename = f.replace(".txt", "").replace("examples_", "")
    theorem_name = ""
    for k in benchmark_lemmas:
        goal_name = os.path.basename(k).split(".")[0]
        locs = benchmark_lemmas[k]
        for l in locs:
            comb_name = l[0].replace("'","") + "_" + str(l[1])+ "_"+l[2]
            split_name = orig_lemma_name.split(lemma_filename + "_")
            if split_name[1] == comb_name:
                theorem_name = goal_name + "_" + l[0].replace("'","")
                original_theorem_name = l[0].replace("'","")
            elif  len(split_name) > 2 and split_name[2] == comb_name:
                theorem_name = goal_name + "_" + l[0].replace("'","")
                original_theorem_name = l[0].replace("'","")
    if theorem_name != "":
        isweaker = is_weaker_than_human(original_theorem_name, lemma, prelude, imports)
        isstronger = is_stronger_than_human(original_theorem_name, all_lemmas[theorem_name], lemma, prelude, imports)
        if isweaker and isstronger:
            return True
        else:
            if isweaker:
                return True
        return False
    return False
    # if theorem_name != "":
    #     # call proverbot to see if the lemma implies it.
    #     pf = open(os.path.join(prelude, "prove_lemma.v"), "w")
    #     for i in imports:
    #         pf.write(i+"\n")
    #     # pf.write(lemma+"\n")
    #     try:
    #         pf.write(all_lemmas[theorem_name])
    #     except:
    #         return False
    #     pf.write("Admitted.\n")
    #     pf.close()
    #     pf = open(os.path.join(prelude, "prove_axiom.txt"), "w")
    #     try:
    #         # pf.write(all_lemmas[theorem_name])
    #         pf.write(lemma)
    #     except:
    #         return False
    #     pf.close()
    #     search_dir = f"{prelude}/search-report"
    #     if os.path.isdir(search_dir):
    #         p1 = shutil.rmtree(search_dir)
    #     proverbot = os.environ['PROVERBOT']
    #     proverbot_cmd = f"timeout 10 {proverbot}src/search_file.py --prelude={prelude} --weightsfile={proverbot}data/polyarg-weights.dat prove_lemma.v --add-axioms={prelude}/prove_axiom.txt -P -o {prelude}/search-report"
    #     print(proverbot_cmd)
    #     p1 = subprocess.getoutput(proverbot_cmd)
    #     op_check = f"cat {prelude}/search-report/*-proofs.txt | grep SUCCESS | grep {theorem_name} -c"
    #     print(op_check)
    #     op_op = subprocess.getoutput(op_check)
    #     print(op_op)
    #     if op_op[0] == "1":
    #         print("here2")
    #         return True
    return False

def is_proof_complete(prelude, imports, proof_cmds, stmts=[]):
    print(proof_cmds)
    with coq_serapy.SerapiContext(
            ["sertop", "--implicit"],    
            None,
            prelude) as coq:
        for imp in imports:
            coq.run_stmt(imp)
        for stmt in stmts:
            coq.run_stmt(stmt)
        try:
            cmds_left, cmds_run = coq.run_into_next_proof(
            proof_cmds)
            _, _ = coq.finish_proof(cmds_left)
            return True
        except coq_serapy.CoqExn:
            return False 
        except:
            return False

def is_stronger_than_human(human_lemma_name, human_lemma, synth_lemma, prelude, imports):
    synth_lemma_name = synth_lemma.split(":")[0].replace("Lemma ", "").strip()
    if synth_lemma[len(synth_lemma)-1] == ".":
        stmts = [synth_lemma, "Admitted."]
    else:
        stmts = [synth_lemma+".", "Admitted."]
    apply_proof_cmds = [human_lemma.replace(human_lemma_name, "humanlemma"), "Proof.",
        "intros.",
        f"apply {synth_lemma_name}.",
        "Qed."]
    is_proof_complete_apply = is_proof_complete(prelude, imports, apply_proof_cmds, stmts)
    rewrite_proof_cmds = [human_lemma.replace(human_lemma_name, "humanlemma"), "Proof.",
        "intros.",
        f"rewrite -> {synth_lemma_name}.",
        "reflexivity.",
        "Qed."]
    is_proof_complete_rewrite = is_proof_complete(prelude, imports, rewrite_proof_cmds, stmts)
    rewrite_proof_cmds = [human_lemma.replace(human_lemma_name, "humanlemma"), "Proof.",
        "intros.",
        f"rewrite <- {synth_lemma_name}.",
        "reflexivity.",
        "Qed."]
    is_proof_complete_rewrite_left = is_proof_complete(prelude, imports, rewrite_proof_cmds, stmts)
    return is_proof_complete_apply or is_proof_complete_rewrite or is_proof_complete_rewrite_left

def is_weaker_than_human(human_lemma_name, synth_lemma, prelude, imports):
    if synth_lemma[len(synth_lemma)-1] == ".":
        name =  synth_lemma 
    else:
        name =  synth_lemma+"."
    apply_proof_cmds = [name, "Proof.",
        "intros.",
        f"apply {human_lemma_name}.",
        "Qed."]
    is_proof_complete_apply = is_proof_complete(prelude, imports, apply_proof_cmds)
    rewrite_proof_cmds = [name, "Proof.",
        "intros.",
        f"rewrite -> {human_lemma_name}.",
        "reflexivity.",
        "Qed."]
    is_proof_complete_rewrite = is_proof_complete(prelude, imports, rewrite_proof_cmds)
    rewrite_proof_cmds = [name, "Proof.",
        "intros.",
        f"rewrite <- {human_lemma_name}.",
        "reflexivity.",
        "Qed."]
    is_proof_complete_rewrite_left = is_proof_complete(prelude, imports, rewrite_proof_cmds)
    return is_proof_complete_apply or is_proof_complete_rewrite or is_proof_complete_rewrite_left

def is_trivial(lemma, prelude, imports):
    proof_cmds = [lemma+".", "Proof.",
        "trivial.",
        "Qed."]
    with coq_serapy.SerapiContext(
            ["sertop", "--implicit"],    
            None,
            prelude) as coq:
        for imp in imports:
            coq.run_stmt(imp)
        cmds_left, cmds_run = coq.run_into_next_proof(
            proof_cmds)
        try:
            _, _ = coq.finish_proof(cmds_left)
            print(f"{lemma} is trivial")
            return True
        except coq_serapy.CoqExn:
            return False        

def simplify_lemma(lemma, prelude, imports):
    if "Lemma :" in lemma:
        lemma = lemma.replace("Lemma :", "Lemma")
    else:
        lemma = "Lemma " + lemma
    lemmaname = lemma.split(":")[0] + ":"
    with coq_serapy.SerapiContext(
            ["sertop", "--implicit"],    
            None,
            prelude) as coq:
        for imp in imports:
            coq.run_stmt(imp)
        coq.run_stmt(lemma + ".")
        coq.run_stmt("simpl.")
        return lemmaname, coq.goals.strip()

def get_proverbot_provable(log_summary, log_obj, prelude, imports, all_lemmas):
    lemmas_so_far = []
    contents = open(log_summary).readlines()
    is_provable = False
    is_useful = False
    for c in contents:
        if ':' in c and '#' in c:
            val = int(c.split(":")[1])
        if "Synthesized Lemmas useful in proving original goal and provable by proverbot" in c:
            is_useful = False
            is_provable = True
            log_obj.no_synth_provable = val
        if "#Generalizations useful in proving original goal and provable by proverbot" in c:
            is_useful = False
            is_provable = True
            log_obj.no_gen_provable = val
        if "# Generalizations :" in c:
            log_obj.total_gen = val
        if "#Synthesized Lemmas not disprovable :" in c:
            log_obj.total_synth = val
        if "#Generalizations useful in proving original goal:" in c:
            is_useful = True
            is_provable = False
            log_obj.no_gen_useful_stuck_provable = val
        if "#Synthesized Lemmas useful in proving original goal:" in c:
            is_useful = True
            is_provable = False
            log_obj.no_syn_useful_stuck_provable = val
        if is_provable and ("Lemma :" in c or "forall" in c):
            # try:
                lemmaname, lemma = simplify_lemma(c.strip(), prelude, imports)
                is_version = is_lemma_version_of_theorem((lemmaname + lemma.replace("\n","")), prelude, all_lemmas, imports)
                if lemma not in lemmas_so_far and not is_version:
                    lemmas_so_far.append(lemma)            
                    log_obj.provable_lemmas.append(lemmaname + lemma.replace("\n",""))
            # except:
                # log_obj.provable_lemmas.append(c.strip())
        if is_useful and ("Lemma :" in c or "forall" in c):
            lemmaname, lemma = simplify_lemma(c.strip(), prelude, imports)
            is_version = is_lemma_version_of_theorem((lemmaname + lemma.replace("\n","")), prelude, all_lemmas, imports)
            if lemma not in lemmas_so_far and not is_version:
                lemmas_so_far.append(lemma)
                log_obj.useful_stuck_provable_lemmas.append(lemmaname + lemma.replace("\n",""))
        if is_useful and is_provable:
            raise Exception("cannot be true at the same time")
    return log_obj, lemmas_so_far

def update_valid_lemmas(log_file, log_obj, lemmas_so_far, prelude, imports, all_lemmas):
    contents = open(log_file).readlines()
    gen_stat_count = 0
    gen_conj = ""
    accum = False
    for i in range(0, len(contents)):
        c = contents[i]
        if "### Generalization Stat ###" in c:
            gen_stat_count += 1
            gen_conj = ""
        if "Generalized Conjecture :" in c:
            gen_conj = c.split("Generalized Conjecture :")[1]
        if gen_stat_count == 1 and "is_prover_provable" in c:
            log_obj.is_stuck_provable = (c.split(":")[1].strip()=="true")
        if "is_valid :" in c and (c.split(":")[1].strip()=="true"):
            lemmaname, lemma = simplify_lemma(gen_conj.strip(), prelude, imports)
            is_version = is_lemma_version_of_theorem((lemmaname + lemma.replace("\n","")), prelude, all_lemmas, imports)
            if lemma not in lemmas_so_far and not is_version:
                lemmas_so_far.append(lemma)
                log_obj.valid_lemmas.append(lemmaname + lemma.replace("\n",""))
        if "Valid Lemmas" in c:
            accum = True
        if "# Lemmas useful to prove original goal" in c:
            accum = False
        if accum and "Lemma :" in c:
            lemmaname, lemma = simplify_lemma(c.strip(), prelude, imports)
            is_version = is_lemma_version_of_theorem((lemmaname + lemma.replace("\n","")), prelude, all_lemmas, imports)
            if lemma not in lemmas_so_far and not is_version:
                lemmas_so_far.append(lemma)
                log_obj.valid_lemmas.append(lemmaname + lemma.replace("\n",""))

def get_imports(fname):
    file = open(fname, 'r')
    lines = file.readlines()
    imports  = []
    for l in lines:
        if "Require Import" in l and "LFind" not in l:
            imports.append(l.strip())
    print(imports)
    return imports

def rank_and_add_to_csv(dir_name, all_lemmas):
    log_file = os.path.join(dir_name, "lfind_log.txt")
    log_summary = os.path.join(dir_name, "lfind_summary_log.txt")
    lfind_state = os.path.join(dir_name, "lfind_state.v")
    if not os.path.isfile(log_file):
        print(f"log not found {log_file}")
        raise MissingLogException(f"Log file {log_file} not found")
    if not os.path.isfile(log_summary):
        raise MissingLogException(f"Summary file {log_file} not found")
    if not os.path.isfile(lfind_state):
        raise MissingLogException(f"State not found file {log_file} not found")
    imports = get_imports(lfind_state)        
    log_obj = LogDetails()
    log_obj.log_dir = dir_name
    log_obj, lemmas_so_far = get_proverbot_provable(log_summary,log_obj, dir_name, imports, all_lemmas)
    update_valid_lemmas(log_file, log_obj, lemmas_so_far, dir_name, imports, all_lemmas)
    return log_obj

def compare_lemmas(lemma):
    return len(lemma.split(",")[1])

def get_ranked_lemmmas(lemma_file, prelude, imports):
    contents = open(lemma_file).readlines()
    log_obj = LogDetails()
    is_provable = False
    is_useful = False
    is_valid = False
    for l in contents:
        if "Provable and Useful in Completing Stuck Goal" == l.strip():
            is_provable = True
        if "Lemma" in l and ":" in l and is_provable:
            istrivial = is_trivial(l, prelude, imports)
            if not istrivial:
                log_obj.provable_lemmas.append(l)
        if "Useful in Completing Stuck Goal" == l.strip():
            is_provable = False
            is_useful = True
        if "Lemma" in l and ":" in l and is_useful:
            istrivial = is_trivial(l, prelude, imports)
            if not istrivial:
                log_obj.useful_stuck_provable_lemmas.append(l)
        if "Valid Lemmas" == l.strip():
            is_valid = True
            is_useful = False
            is_provable = False
        if "Lemma" in l and ":" in l and is_valid:
            istrivial = is_trivial(l, prelude, imports)
            if not istrivial:
                log_obj.valid_lemmas.append(l)
    return log_obj

def sort_and_print_lemmas(log_dir, log_obj):
    f_name = os.path.basename(log_obj.log_dir).replace("_lfind_","")
    l_file = os.path.join(log_dir, f_name)
    f = open(l_file, "w")
    f.write("Provable and Useful in Completing Stuck Goal\n")
    s = sorted(log_obj.provable_lemmas, key=compare_lemmas)
    f.writelines('\n'.join(s))
    f.write("\nUseful in Completing Stuck Goal\n")
    s = sorted(log_obj.useful_stuck_provable_lemmas, key=compare_lemmas)
    f.writelines('\n'.join(s))
    f.write("\nValid Lemmas\n")
    s = sorted(log_obj.valid_lemmas, key=compare_lemmas) 
    f.writelines('\n'.join(s))
    f.close()    
    

def run(lfind_op, log_dir, trivial_ld, trivial):
    op_csv = os.path.join(log_dir, "lfind_benchmark_summary.csv")
    count_total_lfind_logs = 0
    total_lemmas = 0
    missing_lemmas = 0
    missing_lemmas_profile = {}
    provable_by_proverbot = 0
    stuck_state_provable = 0
    log_objs = []
    useful_stuck_provable_lemmas = 0
    matches_human = 0
    stronger_than_human = 0
    weaker_than_human = 0
    for root, dirs, files in os.walk(lfind_op):
        for name in dirs:
            f_name = os.path.join(root, name)
            if os.path.isdir(f_name) and "_lfind_" in f_name:
                benchmark_file = os.path.join(os.path.dirname(f_name),f_name.split("_lfind_")[1].split("_lf_")[0], "lemmafinder_all_lemmas.txt")
                all_lemmas = get_lemmas(benchmark_file)
                lf_name = os.path.basename(f_name).replace("_lfind_","")
                l_file = os.path.join(log_dir, lf_name)          
                count_total_lfind_logs +=1      
                if os.path.isfile(l_file) and trivial:
                    print("here in removing trivial ones")
                    # we need to remove trivial ones
                    lfind_state = os.path.join(f_name, "lfind_state.v")
                    helper_lemma_name, alternate_helper_lemma_name = get_helper_lemma(f_name)
                    try:
                        helper_lemma = all_lemmas[helper_lemma_name]
                        # continue
                    except:
                        try:
                            helper_lemma = all_lemmas[alternate_helper_lemma_name]
                            # helper_lemma_name = alternate_helper_lemma_name
                        except:
                            helper_lemma = ""
                            print(f"helper was not found {helper_lemma_name}")
                            # print(all_lemmas[alternate_helper_lemma_name])
                            print(f_name)
                            print(benchmark_file)
                            # import sys
                            # sys.exit(0) 
                    imports = get_imports(lfind_state)
                    log_obj = get_ranked_lemmmas(l_file, f_name, imports)
                    lemma_synth = []
                    lemma_synth.extend(log_obj.provable_lemmas)
                    lemma_synth.extend(log_obj.useful_stuck_provable_lemmas)
                    lemma_synth.extend(log_obj.valid_lemmas)
                                           
                    log_obj.helper_name = helper_lemma_name 
                    log_obj.helper_lemma = helper_lemma
                    for i in range(0, len(lemma_synth)):
                        l = lemma_synth[i]
                        print(f"helper lemma is {helper_lemma}")
                        print(f"helper lemma is {helper_lemma_name}")
                        if helper_lemma == "":
                            break
                        isweaker = is_weaker_than_human(helper_lemma_name, l, f_name, imports)
                        isstronger = is_stronger_than_human(helper_lemma_name, helper_lemma, l, f_name, imports)
                        if isweaker and isstronger and (not log_obj.matches_human):
                            print(f"similar to user provided lemma {helper_lemma} : {l}")
                            log_obj.matches_human = True
                            log_obj.matched_lemma_loc = i + 1
                            log_obj.matched_lemma = l
                            if "synth" in l:
                                log_obj.top_answer = "S"
                            else:
                                log_obj.top_answer = "G"
                        elif isstronger and (not log_obj.is_stronger_than_human):
                            print(f"stronger than lemma {helper_lemma} : {l}")
                            log_obj.is_stronger_than_human = True
                            log_obj.stronger_lemma = l
                            log_obj.stronger_lemma_loc = i + 1
                            if "synth" in l:
                                log_obj.top_answer = "S"
                            else:
                                log_obj.top_answer = "G"
                        elif isweaker and (not log_obj.is_weaker_than_human):
                            print(f"weaker than lemma {helper_lemma} : {l}")
                            log_obj.is_weaker_than_human = True
                            log_obj.weaker_lemma = l
                            log_obj.weaker_lemma_loc = i + 1
                            if "synth" in l:
                                log_obj.top_answer = "S"
                            else:
                                log_obj.top_answer = "G"
                    log_obj.log_dir = f_name
                    log_obj.is_auto_provable = len(log_obj.provable_lemmas) > 0
                    if log_obj.is_auto_provable:
                        if "synth" in log_obj.provable_lemmas[0]:
                            log_obj.top_answer = "S"
                        else:
                            log_obj.top_answer = "G"
                    sort_and_print_lemmas(trivial_ld, log_obj)
                else:
                    print("here in removing implies original statement")
                    try:
                        log_obj = rank_and_add_to_csv(f_name, all_lemmas)
                        sort_and_print_lemmas(log_dir, log_obj)
                    except MissingLogException:
                        log_obj = None
                        print("missing log")
                        missing_lemmas += 1 
                        missing_lemmas_profile[f_name] = "Log File Missing"
                if log_obj:
                    log_objs.append(log_obj)
                    provable_by_proverbot += int((log_obj.no_gen_provable + log_obj.no_synth_provable) > 0)
                    stuck_state_provable += int(log_obj.is_stuck_provable)
                    useful_stuck_provable_lemmas+=(len(log_obj.useful_stuck_provable_lemmas) > 0)
            if os.path.isdir(f_name) and "_lfind_" not in f_name and "_lf_" in f_name:
                total_lemmas +=1
                log_name = f"_lfind_{name}"
                if not os.path.isdir(os.path.join(root, log_name)):
                    missing_lemmas_profile[f_name] = "_lfind_ was not generated"
        break
    # write_missing_lemmasto_csv(missing_lemmas_profile, log_dir)
    # write_log_objs(op_csv,log_objs)
    if trivial:
        dir_to_write_summary = trivial_ld
    else:
        dir_to_write_summary = log_dir   
        write_missing_lemmasto_csv(missing_lemmas_profile, log_dir)
    write_log_objs(os.path.join(dir_to_write_summary,"summary.csv"), log_objs)
    matches_human = 0
    stronger_than_human = 0
    weaker_than_human = 0
    for o in log_objs:
        matches_human +=o.matches_human
        stronger_than_human +=o.is_stronger_than_human
        weaker_than_human += o.is_weaker_than_human

    print(f"#Lemmas matching humans/#Lemmas: {matches_human}/{total_lemmas-(len(missing_lemmas_profile))}")
    print(f"#Lemmas stronger than humans/#Lemmas: {stronger_than_human}/{total_lemmas-(len(missing_lemmas_profile))}")
    print(f"#Lemmas weaker than humans/#Lemmas: {weaker_than_human}/{total_lemmas-(len(missing_lemmas_profile))}")
    return provable_by_proverbot, total_lemmas, (len(missing_lemmas_profile)), stuck_state_provable, useful_stuck_provable_lemmas


def main():
    args, parser = parse_arguments()
    provable_by_proverbot, total_lemmas, missing_lemmas,stuck_state_provable,useful_stuck_provable_lemmas = run(args.lfind_op, args.log_dir, args.trivial_ld, args.trivial)
    print(f"#Lemmas stuck state provable/#Lemmas: {stuck_state_provable}/{total_lemmas-missing_lemmas}")
    print(f"#Lemmas that are fully provable/#Lemmas: {provable_by_proverbot}/{total_lemmas-missing_lemmas}")
    print(f"#Lemmas that help prove/#Lemmas: {useful_stuck_provable_lemmas}/{total_lemmas-missing_lemmas}")
    print(f"#Lemmas that are missing/#Lemmas: {missing_lemmas}/{total_lemmas}")

if __name__ == "__main__":
    main()
