import argparse
from csv import reader
from email import header
import os
import json
import shutil
import subprocess
import csv
import statistics

from typing import Tuple
from process_logs import *
from tabulate import tabulate
from helper import *
from statistics import mean


def parse_arguments() -> Tuple[argparse.Namespace, argparse.ArgumentParser]:
    parser = argparse.ArgumentParser(
        description=
        "Run and Plot Benchmark Files")
    parser.add_argument('--prelude', default="./")
    parser.add_argument('--logical_directory', default="test")
    parser.add_argument('--log_directory', default="./")
    parser.add_argument('--debug', default=False, action='store_true')
    parser.add_argument('--no-resume', default=False, action='store_true')
    parser.add_argument('--no-quickchick', default=False, action='store_true')
    parser.add_argument('--no-proverbot', default=False, action='store_true')
    parser.add_argument('--synthesizer', default="coqsynth", type=str)
    parser.add_argument('--example_dir', default=None)
    parser.add_argument('--getting_started', default=False, action='store_true')
    parser.add_argument('--small', default=False, action='store_true')
    parser.add_argument('--large', default=False, action='store_true')
    parser.add_argument('--summarize', default=False, action='store_true')
    parser.add_argument('--project', default=False, action='store_true')
    parser.add_argument('-b', '--bench', help='list of benchmarks or projects', type=str, required=True)
    return parser.parse_args(), parser

def get_locations(folder):
    benchmark_file = os.path.join(folder, "lemmafinder_bench.txt")
    with open(benchmark_file, 'r') as j:
     lemma_dict = json.loads(j.read())    
    return lemma_dict, benchmark_file

def get_all_lemmas(folder):
    benchmark_file = os.path.join(folder, "lemmafinder_all_lemmas.txt")
    with open(benchmark_file, 'r') as j:
     all_lemmas = json.loads(j.read())    
    return all_lemmas

def populate_logs_from_file(f_name):
    all_logs = []
    with open(f_name, 'r') as read_obj:
        csv_reader = reader(read_obj)
        header = next(csv_reader)
        for row in csv_reader:
            log_obj = LogDetails()
            log_obj.of_string(row)
            all_logs.append(log_obj)
    return all_logs

def lemma_finder_copy(source_folder, dest_folder) -> None:
    if not os.path.isdir(dest_folder):
        shutil.copytree(source_folder, dest_folder)

def write_lemmafinder_content(file, content):
    with open(file,"w") as f:
        f.write("".join(content))

def write_errors_to_csv(csv_file, content):
    column_names = ["Original Statement", "Required Helper Lemma", "Make Cmd", "Stuck State"]
    with open(csv_file, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(column_names)
        writer.writerows(content)

def get_stuck_state(fname):
    try:
        with open(fname, 'r') as j:
            content = j.readlines()
            for l in content:
                if "lfind_state" in l:
                    return l
    except Exception as e:
        print(e)
    return ""

def clean_quickchick_tmp_dir():
    shutil.rmtree('dir_path')

def run(source_folder, helper_lemma_dict, lfind_decl):
    attempted = 0
    solved = 0
    for file in helper_lemma_dict:
        file_name = os.path.basename(file)
        helper_lemma_locations = helper_lemma_dict[file]
        file = os.path.join(source_folder, file)
        if ".v" in file :
            with open(file) as f:
                content = f.readlines()
            for location in helper_lemma_locations:
                lemma_line = location[1]
                lemma_name = location[2].replace("'","")
                lfind_content = [lfind_decl]
                lfind_content.append("\n") 
                lfind_content.extend(content[:lemma_line])
                stuck_folder = os.path.join(os.path.dirname(source_folder),"_lfind_" + str(os.path.basename(source_folder))+"_lf_" + os.path.splitext(file_name)[0] + "_" + location[0].replace("'","") + "_" + str(location[1])+"_" + lemma_name)
                
                lfind_summary_log = os.path.join(stuck_folder, "lfind_summary_log.txt")
                # is_run_make = True
                if os.path.isdir(stuck_folder):
                    attempted += 1
                if os.path.isdir(stuck_folder) and os.path.isfile(lfind_summary_log):
                    solved += 1
    print(f'solved: {solved}/{attempted} attempted')

def table_1_header(dataset):
    return [" "] + dataset

def table_1_setup(dataset_type_small):
    if dataset_type_small:
        data = [
                ["#Theorems",86,40,9],
                ["# Evaluation Locations", 14, 5,4]
               ]
    else:
        data = [
                ["#Theorems",86,40,1,9],
                ["# Evaluation Locations", 140, 62 ,1, 19]
               ]
    return data

def table_1_from_logs(all_logs):
    cat_1 = []
    human_1 = []
    human_5 = []
    human_10 = []
    human_gt_10 = []
    # stronger_1 = []
    summary = []
    if all_logs:
        bench_logs = all_logs
    else:
        bench_logs = []
    bench_cat_1 = 0
    bench_human_1 = 0
    bench_human_5 = 0
    bench_human_10 = 0
    bench_human_gt_10 = 0
    # bench_stronger_1 = 0
    bench_sum = 0
    for log_obj in bench_logs:
        if log_obj.is_auto_provable:
            bench_cat_1 +=1
            bench_sum +=1
        elif log_obj.matches_human:
            if log_obj.matched_lemma_loc == 1:
                bench_human_1 += 1
                bench_sum +=1
            elif log_obj.matched_lemma_loc > 1 and log_obj.matched_lemma_loc <= 5:
                bench_human_5 +=1
                bench_sum +=1
            elif log_obj.matched_lemma_loc > 5 and log_obj.matched_lemma_loc <= 10:
                bench_human_10 += 1
                bench_sum +=1
            else:
                bench_human_gt_10 +=1
                bench_sum +=1
        else:
            print(f'not matched: {log_obj.log_dir}')
        # elif log_obj.is_stronger_than_human and log_obj.stronger_lemma_loc == 1:
        #     bench_stronger_1 += 1
        #     bench_sum +=1
    cat_1.append(bench_cat_1)
    human_1.append(bench_human_1)
    human_5.append(bench_human_5)
    human_10.append(bench_human_10)
    human_gt_10.append(bench_human_gt_10)
    # stronger_1.append(bench_stronger_1)
    summary.append(f"{bench_sum}/{len(bench_logs)}")
    data = [ ["# fully proven lemma and goal"] + cat_1,
             ["# else human match in top 1 "] + human_1,
             ["# else human match in top 5 "] + human_5,
             ["# else human match in top 10"] + human_10,
             ["# else human match > 10"] + human_gt_10,
            #  ["# else more general than human lemma in top 1"] + stronger_1,
             ["Summary"] + summary
          ]
    return data

def create_figure_7(f_name, generated, after_f_1, after_f_2):
    dataset = {
        "#Generated": generated,
        "#After Filter 1": after_f_1,
        "#After Filter 2": after_f_2,
    }
    create_pct_diff_plot_2(
            list(dataset.values()),
            dataset.keys(),        
            save_path=f_name,
            xlabel="#Lemmas",
            ylabel="CDF",
            location="lower right",
            log_scale=False,
            colors=["#66c2a4","#00441b","#238b45"],
            linestyles=["-", "--", ":"],
            axes_font_size=15,
            tick_label_size=12,
            legend_size=15,
            scientific_axis=False,
    )

def create_figure_6(f_name, total_times, time_to_cat_1s):
    to_plot = {
"Time to category 1":time_to_cat_1s,
"Total time":total_times,
}

    create_pct_diff_plot_2(
        list(to_plot.values()),
        to_plot.keys(),
        save_path=f_name,
        xlabel="Runtime (minutes)",
        ylabel="Cumulative Distribution\nFunction (CDF)",
        location="lower right",
        log_scale=False,
        colors=["#66c2a4","#00441b",],
        linestyles=["-", "-."],
        axes_font_size=12,
        tick_label_size=12,
        legend_size=15,
    )

def plot_table_1_fig_6_7(benchmarks, is_small, all_logs, log_dir,all_total_times,all_time_tocat_1s,all_total_lemmas,all_total_afterquickchick,all_total_after_other_filters):
    headers = table_1_header(benchmarks)
    body_data = table_1_from_logs(all_logs, benchmarks)
    with open(os.path.join(log_dir,"table1"), 'w') as outputfile:
        outputfile.write(tabulate(body_data, headers=headers, tablefmt="grid"))
    print(f"Table 1 saved at {os.path.join(log_dir,'table_1')}")
    print("Table 1: Results")
    print(tabulate(body_data, headers=headers, tablefmt="grid"))
    figure_6_file = os.path.join(log_dir,'figure_6.pdf')
    print(f"Figure 6 saved at {figure_6_file}")
    print(f"Median Total Time: {statistics.median(all_total_times)} min")
    print(f"Median Time to Category 1: {statistics.median(all_time_tocat_1s)} min")
    create_figure_6(figure_6_file, all_total_times,all_time_tocat_1s)
    figure_7_file = os.path.join(log_dir,'figure_7.pdf')
    print(f"Figure 7 saved at {figure_7_file}")
    print(f"Median #Generated: {statistics.median(all_total_lemmas)} lemmas")
    print(f"Median #After filter 1: {statistics.median(all_total_afterquickchick)} lemmas")
    print(f"Median #After filter 2: {statistics.median(all_total_after_other_filters)} lemmas")
    create_figure_7(figure_7_file, all_total_lemmas, all_total_afterquickchick, all_total_after_other_filters)

def compare_size_of_sketch_synth(all_logs, benchmarks, log_dir):
    count_success = 0
    synth_lemm_term = []
    synth_size = []
    myth_size = []
    ratio_size_of_synth_full = []
    for bench in benchmarks:
        for log_obj in all_logs[bench]:
            if log_obj.is_success:
                success_lemma = ""
                if log_obj.is_auto_provable:
                    lfind_summary = os.path.join(log_dir, bench, os.path.basename(log_obj.log_dir).replace("_lfind_",""))
                    contents = open(lfind_summary).readlines()
                    for l in contents:
                        if "Lemma " in l and "forall" in l:
                            success_lemma = l
                            break 
                elif log_obj.matches_human:
                    if log_obj.matched_lemma_loc <= 10 and log_obj.matched_lemma_loc >= 0:
                        success_lemma = log_obj.matched_lemma
                elif log_obj.is_stronger_than_human:
                    if log_obj.stronger_lemma_loc < 10 and log_obj.stronger_lemma_loc >=0:
                        success_lemma = log_obj.stronger_lemma
                success_lemma = success_lemma.replace("Lemma", "Lemma :")
                if log_obj.top_answer.strip() == 'S' and log_obj.is_success:
                    count_success +=1
                    lfind_log = os.path.join(log_obj.log_dir,"lfind_log.txt")
                    if os.path.exists(lfind_log):
                        contents = open(lfind_log).readlines()
                        previous = ""
                        myth_term = ""
                        for l in contents:
                            if l.strip() == success_lemma.strip():
                                myth_term = previous.replace("Myth Term :", "").strip()
                                break
                            else:
                                previous = l
                        size_of_synth = 0
                        size_of_myth_term = 0
                        success_lemma = success_lemma.split(",")[1]
                        try:
                            size_of_synth = getSizeOfNestedList(loads(success_lemma))
                        except:
                            size_of_synth = getSizeOfNestedList(loads ("(" + success_lemma + ")"))
                        try:
                            size_of_myth_term = getSizeOfNestedList(loads(myth_term))
                        except:
                            size_of_myth_term = getSizeOfNestedList(loads ("(" + myth_term + ")"))
                        curr_synth_myth_data = [success_lemma, myth_term, size_of_synth, size_of_myth_term]
                        synth_lemm_term.append(curr_synth_myth_data)
                        synth_size.append(size_of_synth-size_of_myth_term)
                        myth_size.append(size_of_myth_term)
                        ratio_size_of_synth_full.append(size_of_myth_term/size_of_synth)
    print(f"Median Size of sketch {statistics.median(synth_size)}")
    print(f"Median Size of myth term is {statistics.median(myth_size)}")
    print(f"Average percentage of synthesized term {statistics.mean(ratio_size_of_synth_full)}")

def get_lfind_decl(args):
    lfind_decl = "Load LFindLoad.\nFrom lfind Require Import LFind.\nUnset Printing Notations.\nSet Printing Implicit.\n"
    if args.no_quickchick:
        lfind_decl += "Unset Lfind QuickChick.\n"
    if args.no_proverbot:
        lfind_decl += "Unset Lfind Proverbot.\n"
    return lfind_decl

def main() -> None:
    args, parser = parse_arguments()
    if args.synthesizer not in ["coqsynth", "myth"]:
        print("Synthesizer must be either coqsynth or myth")
        exit(1)
    print(f"Synthesizer: {args.synthesizer}")
    benchmark_all = [item for item in args.bench.split(',')]
    lfind_decl = get_lfind_decl(args)
    
    if args.getting_started:
        # run LFIND on the given repo
        helper_lemma_dict, benchmark_file = get_locations(args.prelude)
        run(args.prelude, helper_lemma_dict, lfind_decl)
        print("Completed running on the given dataset")
        # # process log files from the repo
        # log_objs, total_times, time_to_cat_1s, total_lemmas, total_afterquickchick, total_after_other_filters= run_process_logs(args.log_directory, helper_lemma_dict, args.project, args.prelude)
        # print(len(log_objs))
        # print(len(log_objs[0].provable_lemmas))
        # print("-----------------------------------------------")
        # print("Run complete")        
        # if args.getting_started:
        #     print("Top Lemmas:")
        #     cat_1_lemma = log_objs[0].provable_lemmas[0].rstrip('\n')
        #     print(f"(cat 1) {cat_1_lemma}")
        #     print(f"(cat 2) {log_objs[0].useful_stuck_provable_lemmas[0]}")
        #     print(f"(cat 2) {log_objs[0].useful_stuck_provable_lemmas[1]}")
        #     print(f"Runtime: {statistics.median(total_times)} min")
        # print("-----------------------------------------------")

if __name__ == "__main__":
    main()