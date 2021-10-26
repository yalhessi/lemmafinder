import argparse
import os
import csv

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

    def row(self):
        return [self.log_dir,self.is_stuck_provable,self.no_gen_provable,self.no_synth_provable, self.no_gen_useful_stuck_provable,self.no_syn_useful_stuck_provable,len(self.valid_lemmas),""]

def parse_arguments():
    parser = argparse.ArgumentParser(
        description=
        "Rank and Generate CSV")
    parser.add_argument('--lfind_op', default="test")
    parser.add_argument('--log_dir', default=".")
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
    column_names = ["FileName", "Stuck State Provable", "#Fully Provable G", "#Fully Provable S", "#Proving stuck state (G)","#Proving stuck state (S)", "#Valid Lemmas", "Human Lemma Location"]
    with open(csv_file, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(column_names)
        s = sorted(log_objs, key=sort_logs_by_goal_no)
        for log_obj in s:
            writer.writerow(log_obj.row())

class MissingLogException(Exception):
    def __init__(self, message):
        super().__init__(message)


def get_proverbot_provable(log_summary, log_obj):
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
            log_obj.provable_lemmas.append(c.strip())
        if is_useful and ("Lemma :" in c or "forall" in c):
            if c not in log_obj.provable_lemmas:
                log_obj.useful_stuck_provable_lemmas.append(c.strip())
        if is_useful and is_provable:
            raise Exception("cannot be true at the same time")
    return log_obj

def update_valid_lemmas(log_file, log_obj):
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
            if gen_conj not in log_obj.provable_lemmas and gen_conj not in log_obj.useful_stuck_provable_lemmas:
                log_obj.valid_lemmas.append(gen_conj)
        if "Valid Lemmas" in c:
            accum = True
        if "# Lemmas useful to prove original goal" in c:
            accum = False
        if accum and "Lemma :" in c:
            if gen_conj not in log_obj.provable_lemmas and gen_conj not in log_obj.useful_stuck_provable_lemmas:
                log_obj.valid_lemmas.append(c.strip())


def rank_and_add_to_csv(dir_name):
    log_file = os.path.join(dir_name, "lfind_log.txt")
    log_summary = os.path.join(dir_name, "lfind_summary_log.txt")
    if not os.path.isfile(log_file):
        raise MissingLogException(f"Log file {log_file} not found")
    if not os.path.isfile(log_summary):
        raise MissingLogException(f"Summary file {log_file} not found")
    log_obj = LogDetails()
    log_obj.log_dir = dir_name
    log_obj = get_proverbot_provable(log_summary,log_obj)
    update_valid_lemmas(log_file, log_obj)
    return log_obj

def compare_lemmas(lemma):
    return len(lemma.split(",")[1])

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
    

def run(lfind_op, log_dir):
    op_csv = os.path.join(log_dir, "lfind_benchmark_summary.csv")
    count_total_lfind_logs = 0
    total_lemmas = 0
    missing_lemmas = 0
    missing_lemmas_profile = {}
    provable_by_proverbot = 0
    stuck_state_provable = 0
    log_objs = []
    useful_stuck_provable_lemmas = 0
    for root, dirs, files in os.walk(lfind_op):
        for name in dirs:
            f_name = os.path.join(root, name)
            if os.path.isdir(f_name) and "_lfind_" in f_name:                
                count_total_lfind_logs +=1
                try:
                    log_obj = rank_and_add_to_csv(f_name)
                    provable_by_proverbot += int((log_obj.no_gen_provable + log_obj.no_synth_provable) > 0)
                    stuck_state_provable += int(log_obj.is_stuck_provable)
                    assert((log_obj.no_gen_provable + log_obj.no_synth_provable) == len(log_obj.provable_lemmas))
                    useful_stuck_provable_lemmas+=(len(log_obj.useful_stuck_provable_lemmas) > 0)
                    log_objs.append(log_obj)
                    sort_and_print_lemmas(log_dir, log_obj)
                except MissingLogException:
                    missing_lemmas += 1 
                    missing_lemmas_profile[f_name] = "Log File Missing"
            if os.path.isdir(f_name) and "_lfind_" not in f_name and "_lf_" in f_name:
                total_lemmas +=1
                log_name = f"_lfind_{name}"
                if not os.path.isdir(os.path.join(root, log_name)):
                    missing_lemmas_profile[f_name] = "_lfind_ was not generated"
        break
    write_missing_lemmasto_csv(missing_lemmas_profile, log_dir)
    write_log_objs(op_csv,log_objs)
    return provable_by_proverbot, total_lemmas, (len(missing_lemmas_profile)), stuck_state_provable, useful_stuck_provable_lemmas


def main():
    args, parser = parse_arguments()
    provable_by_proverbot, total_lemmas, missing_lemmas,stuck_state_provable,useful_stuck_provable_lemmas = run(args.lfind_op, args.log_dir)
    print(f"#Lemmas stuck state provable/#Lemmas: {stuck_state_provable}/{total_lemmas-missing_lemmas}")
    print(f"#Lemmas that are fully provable/#Lemmas: {provable_by_proverbot}/{total_lemmas-missing_lemmas}")
    print(f"#Lemmas that help prove/#Lemmas: {useful_stuck_provable_lemmas}/{total_lemmas-missing_lemmas}")
    print(f"#Lemmas that are missing/#Lemmas: {missing_lemmas}/{total_lemmas}")

if __name__ == "__main__":
    main()
