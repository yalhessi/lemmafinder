import argparse
import os
import json
import shutil

from typing import Tuple

lfind_decl = "From lfind Require Import LFind."

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

def lemma_finder_copy(source_folder, dest_folder) -> None:
    print(dest_folder)
    if os.path.isdir(dest_folder):
        shutil.rmtree(dest_folder)
    shutil.copytree(source_folder, dest_folder)

def write_lemmafinder_content(file, content):
    print(file)
    with open(file,"w") as f:
        f.write("".join(content))

def run(source_folder, helper_lemma_dict, log_directory):
    counter = 0
    all_lemmas = 0
    filtered_helper_lemma_dict = {}
    for file in helper_lemma_dict:
        file_name = os.path.basename(file)
        print(file_name)
        helper_lemma_locations = helper_lemma_dict[file]
        all_lemmas += len(helper_lemma_locations)
        if "Lists" in file:
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
                write_lemmafinder_content(os.path.join(destination_folder, file_name),lfind_content)
                log_file = f"{log_directory}/lfind_benchmark_log"
                make_cmd = f"cd {destination_folder} && make > {log_file}"
                os.system(make_cmd)
                contents = open(log_file).read()
                if "lemmafinder_example_generation_success" in contents:
                    print("Success: " + location[2])
                    counter += 1
                    if file in filtered_helper_lemma_dict:
                        filtered_helper_lemma_dict[file].append(location)
                    else:
                        filtered_helper_lemma_dict[file] = [location]
            write_lemmafinder_content(os.path.join(destination_folder, file_name),content)
    return filtered_helper_lemma_dict, counter, all_lemmas

def main() -> None:
    args, parser = parse_arguments()
    helper_lemma_dict = get_locations(args.prelude)
    print(helper_lemma_dict)
    filtered_helper_lemmas, total_lemmas, all_lemmas = run(args.prelude, helper_lemma_dict, args.log_directory)
    print(filtered_helper_lemmas)
    print(f"#Lemmas w atleast one helper/#Lemmas: {total_lemmas}/{all_lemmas} in {len(filtered_helper_lemmas)} coq files in 78 projects")


if __name__ == "__main__":
    main()
