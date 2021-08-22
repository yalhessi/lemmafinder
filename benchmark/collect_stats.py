#!/usr/bin/env python3

import argparse
import os
import json

from typing import Tuple

def parse_arguments() -> Tuple[argparse.Namespace, argparse.ArgumentParser]:
    parser = argparse.ArgumentParser(
        description=
        "Count the number of proofs that uses helper lemma")
    parser.add_argument('--prelude', default=".")
    parser.add_argument('--output', default=".")
    return parser.parse_args(), parser

def get_all_lemmas(folder):
    lemmas = {}
    lemma_name_content = {}
    no_lemmas = 0
    lemma_name = ""
    lemma_content = ""
    for directory, subdirectories, files in os.walk(folder):
        for file in files:
            if file.endswith(".v"):
                try:
                    with open(os.path.join(directory, file)) as f:
                        for line in f:
                            if ("Lemma" in line or "Theorem" in line) and ("forall" in line):
                                lemma_name = line.split()[1]
                                lemma_content = line
                            elif ("Proof" in line or "Admitted" in line) and (len(lemma_name) > 0):
                                lemmas[lemma_name] = 1
                                lemma_name_content[lemma_name] = lemma_content.replace("\n","")
                                no_lemmas +=1
                                lemma_name = ""
                                lemma_content = ""
                            else:
                                lemma_content = lemma_content + line
                except Exception as e:
                    print(e)
                    print (f"Error processing {directory}/{file}")
    return lemmas, no_lemmas, lemma_name_content

def count_file(file, lemma_names, lemma_files_names):
    count_helper = 0
    lemma_name = ""
    line_number = -1
    try:
        with open(file) as f:
            start_proof = False
            for line in f:
                line_number+=1
                if start_proof:
                    content = line.split()
                    index = 0
                    helper_indices = []
                    for c in content:
                        if "rewrite"==c or "apply"==c:
                            # if len(content) > index + 2 and content[index+2] != "with":
                            if len(content) > index + 1 and (content[index+1].replace('.','')) in lemma_names:
                                helper_indices.append((index+1,content[index+1].replace('.','')))
                            elif len(content) > index + 2 and (content[index+2].replace('.','')) in lemma_names:
                                helper_indices.append((index+2, content[index+2].replace('.','')))
                        index+=1
                    helper_indices_len = 0
                    while helper_indices_len < len(helper_indices):
                        if file not in lemma_files_names:
                            lemma_files_names[file] = []
                        lemma_files_names[file].append((lemma_name,line_number,helper_indices[helper_indices_len][1]))
                        helper_indices_len += 1
                        count_helper+=1
                        # start_proof = False
                if ("Lemma" in line or "Theorem" in line or "Corollary") and ("forall" in line):
                    lemma_name = line.split()[1]
                if "Proof" in line:
                    start_proof = True
                if "Qed" in line or "Admitted" in line:
                    start_proof = False
    except Exception as e:
        print(e)
        print (f"Error processing {file}")
    return count_helper

def count(folder, output_folder):
    no_coq_files = 0
    no_with_helper = 0
    lemmas, no_lemmas, lemma_content = get_all_lemmas(folder)
    write_lemmas(lemma_content, output_folder)
    lemma_files_names = {}
    for directory, dirs, files in os.walk(folder):
        for file in files:
            if file.endswith(".v"):
                no_coq_files += 1
                no_with_helper += count_file(os.path.join(directory, file), lemmas, lemma_files_names)
    return no_coq_files,no_with_helper,no_lemmas, lemma_files_names

def write_lemmas(content, output_dir):
    with open(os.path.join(output_dir,"lemmafinder_all_lemmas.txt"), "w") as f:
        f.write(json.dumps(content))

def write_op(lemma_file_name, output_dir):
    with open(os.path.join(output_dir,"lemmafinder_bench.txt"), "w") as f:
        f.write(json.dumps(lemma_file_name))
        # for k in lemma_file_name:
        #     f.write(f"{k}:[{lemma_file_name[k]}]\n")


def main() -> None:
    args, parser = parse_arguments()
    no_coq_files, no_with_helper, total_lemmas, lemma_file_names = count(args.prelude, args.output)
    write_op(lemma_file_names,args.output)
    print(f"#Lemmas w atleast one helper/#Lemmas: {no_with_helper}/{total_lemmas} in {no_coq_files} coq files in 78 projects")


if __name__ == "__main__":
    main()
