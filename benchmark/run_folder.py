import argparse
import os
import json
import shutil

from typing import Tuple

lfind_decl = "From lfind Require Import LFind.\nUnset Printing Notations.\nSet Printing Implicit.\n"

def parse_arguments() -> Tuple[argparse.Namespace, argparse.ArgumentParser]:
    parser = argparse.ArgumentParser(
        description=
        "Run benchmark files")
    parser.add_argument('--prelude', default=".")
    parser.add_argument('--logical_directory', default="test")
    parser.add_argument('--log_directory', default=".")
    return parser.parse_args(), parser

def get_locations(folder):
    benchmark_file = os.path.join(folder, "lemmafinder_bench.txt")
    with open(benchmark_file, 'r') as j:
     lemma_dict = json.loads(j.read())    
    return lemma_dict

def get_all_lemmas(folder):
    benchmark_file = os.path.join(folder, "lemmafinder_all_lemmas.txt")
    with open(benchmark_file, 'r') as j:
     all_lemmas = json.loads(j.read())    
    return all_lemmas

def lemma_finder_copy(source_folder, dest_folder) -> None:
    print(dest_folder)
    if os.path.isdir(dest_folder):
        shutil.rmtree(dest_folder)
    shutil.copytree(source_folder, dest_folder)

def write_lemmafinder_content(file, content):
    print(file)
    with open(file,"w") as f:
        f.write("".join(content))

def run(source_folder, helper_lemma_dict, log_directory, all_lemmas_from_file):
    counter = 0
    all_lemmas = 0
    filtered_helper_lemma_dict = {}
    for file in helper_lemma_dict:
        file_name = os.path.basename(file)
        print(file_name)
        helper_lemma_locations = helper_lemma_dict[file]
        all_lemmas += len(helper_lemma_locations)
        # if "Lists" in file:
        with open(file) as f:
            content = f.readlines()
        for location in helper_lemma_locations:
            lemma_line = location[1]
            lemma_name = location[2]
            lfind_content = [lfind_decl]
            lfind_content.append("\n") 
            lfind_content.extend(content[:lemma_line])
            current_line = content[lemma_line]
            c_line_content = current_line.split(".")
            c_modified_content = []
            destination_folder = os.path.join(os.path.dirname(source_folder),str(os.path.basename(source_folder))+"_lf_" + os.path.splitext(file_name)[0] + "_" + lemma_name)
            lemma_finder_copy(source_folder, destination_folder)
            for i in range(0,len(c_line_content)):
                if lemma_name in c_line_content[i]:
                    c_modified_content.append("lfind")
                else:
                    c_modified_content.append(c_line_content[i])
            lfind_content.append(". ".join(c_modified_content))
            lfind_content.append("Admitted.\n")
            next_valid_index_found = False
            index = lemma_line + 1
            while not next_valid_index_found:
                if "Qed" in content[index] or "Admit" in content[index]:
                    next_valid_index_found = True
                index = index + 1
            lfind_content.extend(content[index:])
            print(f"destination folder is {destination_folder}")
            write_lemmafinder_content(os.path.join(destination_folder, file_name),lfind_content)
            log_file = f"{log_directory}/lfind_benchmark_log"
            make_cmd = f"cd {destination_folder} && make > {log_file}"
            print(make_cmd)
            os.system(make_cmd)
            contents = open(log_file).read()
            # import sys
            # sys.exit(0)
            if "lemmafinder_example_generation_success" in contents:
                print("Success: " + location[2])
                # get log file and write it in the log_directory
                try:
                    log_folder = os.path.join(os.path.dirname(source_folder),"_lfind_" + str(os.path.basename(source_folder))+"_lf_" + os.path.splitext(file_name)[0] + "_" + lemma_name)
                    lfind_summary_log = os.path.join(log_folder, "lfind_summary_log.txt")
                    lfind_log = os.path.join(log_folder, "lfind_log.txt")
                    with open(lfind_summary_log, 'r') as j:
                        lfind_log_content = j.read()
                    content_to_append = f"Theorem statement:\n{all_lemmas_from_file[location[0]]}\n\nRequired Helper Statement:\n{all_lemmas_from_file[location[2]]}\n"
                    lfind_log_w = os.path.join(log_directory, f"{location[0]}_{location[1]}_{location[2]}")
                    with open(lfind_log_w, "w") as w:
                        w.write(content_to_append)
                        w.write(lfind_log_content)
                        w.write(f"\nMore log here {lfind_log}\n")
                        w.write(f"Original Coq file here {file}\n")
                        w.close()
                    counter += 1
                    if file in filtered_helper_lemma_dict:
                        filtered_helper_lemma_dict[file].append(location)
                    else:
                        filtered_helper_lemma_dict[file] = [location]
                except:
                    print("error processing this")
            # import sys
            # sys.exit(0)
        write_lemmafinder_content(os.path.join(destination_folder, file_name),content)
            
    return filtered_helper_lemma_dict, counter, all_lemmas

def main() -> None:
    args, parser = parse_arguments()
    helper_lemma_dict = get_locations(args.prelude)
    all_lemmas_from_file = get_all_lemmas(args.prelude)
    print(helper_lemma_dict)
    filtered_helper_lemmas, total_lemmas, all_lemmas = run(args.prelude, helper_lemma_dict, args.log_directory, all_lemmas_from_file)
    print(filtered_helper_lemmas)
    print(f"#Lemmas w atleast one helper/#Lemmas: {total_lemmas}/{all_lemmas} in {len(filtered_helper_lemmas)} coq files in 78 projects")


if __name__ == "__main__":
    main()
