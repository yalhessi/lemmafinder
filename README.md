Coq Lemma Synthesis Plugin
---------------------------
These instructions were tested only in macos.

Install the following software:

- opam 2.0.7
    - Download https://github.com/ocaml/opam/releases/download/2.0.7/opam-2.0.7-x86_64-macos and run `sudo install <downloaded file> /usr/local/bin/opam`
    - check installation using opam --version (it should say 2.0.7)
- opam update
- opam repo add coq-released https://coq.inria.fr/opam/released
- opam switch create 4.07.1+flambda
- opam install core=v0.12.4
- opam install menhir=20200624
- opam install dune=2.7.1
- opam install coq=8.11.2
- opam install coq-of-ocaml=2.1.0
- opam install coq-serapi=8.11.0+0.11.0
- opam install coq-quickchick=1.3.2


## Additional Setup
We need to setup the following packages before we can run lemmafinder.

### Proverbot
We use proverbot to check if the synthesized or generalized lemma is provable or can help prove the current stuck state.

1. `git clone --recurse-submodules https://github.com/UCSD-PL/proverbot9001.git`
    - git branch should point to master

2. For Mac users ONLY: In `Makefile` replace `cp dataloader/target/release/libdataloader.so src/dataloader.so` with `cp dataloader/target/release/libdataloader.dylib src/dataloader.so`.

3. mkdir proverbot9001/dataloader/.cargo

4. cd proverbot9001/dataloader/.cargo && vi config

5. Paste the following: `[target.x86_64-apple-darwin]
rustflags = [
  "-C", "link-arg=-undefined",
  "-C", "link-arg=dynamic_lookup",
]`


See https://pyo3.rs/v0.5.3/ for why we need this.

6. Comment lines 16-23 in `setup.sh`

7. Ensure you have git, opam, rustup, graphviz, libgraphviz-dev, python3.7, python3.7-dev and python3.7-pip installed.

8. run `make setup`


### Myth
Myth is a Type-and-example-driven program synthesis engine. We use myth to synthesize expressions which are used in constructing useful lemmas.

1. `git clone git@github.com:AishwaryaSivaraman/myth.git`

2. make


### AST-Rewriter
Myth supports only a part of the ocaml syntax. We need a translator that takes in `.ml` file generated from Coq extraction to a format that is compatible/can parse with myth.

1. `git clone git@github.com:AishwaryaSivaraman/astrewriter.git`

2. dune build && dune install

### Lemmafinder
We are now ready to make this project.
Run `cd lemmafinder && dune build && dune install`

## Environment Setup
In the folder that you run make or coqc export the following environment variable

```
export PROVERBOT=<path to proverbot folder>
export MYTH=<path to myth folder>/synml.native
export COQOFOCAML=/Users/<username>/.opam/4.07.1+flambda/bin/coq-of-ocaml
export REWRITE=<path to ast_rewriter>/_build/default/bin/main.exe
```


## Running lemma finder on a particular proof
<em> Note, the tool requires that the original project folder has run `make`</em>

To run ```lfind``` in a proof you need to add the following

```
From lfind Require Import LFind.
Unset Printing Notations.
Set Printing Implicit.
```

In the proof where u are stuck, add `lfind.` tactic and run `make` again in the folder.

### Example:
1. cd `benchmark/bench_rev_append` && make.
This should first make the existing coq file.

2. Uncomment `lfind` in line 47.

3. Run `make`. If the setup is done correctly, this should run the lemma finder in ~30 min and at the end of the run you should see  `Error: LFIND Successful`. The output of this run is saved in `benchmark/_lfind_bench_rev_append`.
You can find the results of the run in `benchmark/_lfind_bench_rev_append/lfind_summary_log.txt`. You can find debug logs in `benchmark/_lfind_bench_rev_append/lfind_debug_log.txt`


## Evaluating Lemma Finder

`cd benchmarks/logical_foundations && make cd ..`

`python3 benchmark/run_folder.py --prelude=<full path to logical_foundations> --log_directory=<full path to log directory>`

This should run on 31 theorems that require helper lemma and output how many of were able to identify helper lemmas. You should find the output files in the --log_directory. 