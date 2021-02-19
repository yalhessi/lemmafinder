Coq Lemma Synthesis Plugin
---------------------------

Software Versions:

- Dune 2.7
- Coq 8.11.2
- opam switch 4.07.1+flambda

## Environment Setup
In the folder that you run make or coqc export the following environment variable

```
export PROVERBOT=<path to proverbot folder>
```

## How to build and install

```
$ dune build
```

```
$ dune install
```


## Coq 
To run ```lfind``` in a proof you need to add the following

```
From lfind Require Import LFind.
Unset Printing Notations.
Set Printing Implicit.
```

