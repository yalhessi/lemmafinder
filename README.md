Coq Lemma Synthesis Plugin
---------------------------
These instructions were tested only in Mac.

Install the following software:

- opam 2.0.7
- opam switch 4.07.1+flambda
- Dune 2.7.1
- Coq 8.11.2
- coqofocaml 2.1.0
- coq-serapi 8.11.0+0.11.0
- coq-quickchick           1.3.2


## Additional Setup
We need to setup the following packages before we can run lemmafinder. 

### Proverbot
We use proverbot to check if the synthesized or generalized lemma is provable or can help prove the current stuck state. 

1. git clone master branch from `https://github.com/UCSD-PL/proverbot9001.git`

2. Within src folder git clone `https://github.com/HazardousPeach/coq_serapy`

3. In `Makefile` replace ` curl -o data/polyarg-weights.dat proverbot9001.ucsd.edu/downloads/weights-10-27-2020.dat` with `curl -o data/polyarg-weights.dat proverbot9001.ucsd.edu/downloads/weights-latest.dat`

4. In `Makefile` replace `cp dataloader/target/release/libdataloader.so src/dataloader.so` with `cp dataloader/target/release/libdataloader.dylib src/dataloader.so` (This is for Mac users).

5. In `src/search_file.py` replace `except CoqExn:                             axiom_name = coq_serapy.lemma_name_from_statement(` with `except serapi_instance.CoqExn:                                 axiom_name = serapi_instance.lemma_name_from_statement(` 

6. Install rust-nightly and follow instructions here https://pyo3.rs/v0.5.3/. Specifically, you need to create config file mentioned, in proverbot9001/dataloader/dataloader-core/.cargo/.

7. Now follow instructions in `https://github.com/UCSD-PL/proverbot9001` to make the project.

### Myth
Myth is a Type-and-example-driven program synthesis engine. We use myth to synthesize expressions which are used in constructing useful lemmas.

1. git clone https://github.com/AishwaryaSivaraman/myth.git

2. Follow instructions in https://github.com/AishwaryaSivaraman/myth to install myth


### AST-Rewriter
Myth supports only a part of the ocaml syntax. We need a translator that takes in `.ml` file generated from Coq extraction to a format that is compatible/can parse with myth. 

1. git clone `https://github.com/AishwaryaSivaraman/astrewriter.git`

2. dune build && dune install

### Lemmafinder
We are now ready to make this project. Run `dune build && dune install`

## Environment Setup
In the folder that you run make or coqc export the following environment variable

```
export PROVERBOT=<path to proverbot folder>
export MYTH=<path to myth folder>
export COQOFOCAML=<path to coqofocaml folder>
export REWRITE=<path to ast_rewriter>
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

TODO: Add example
