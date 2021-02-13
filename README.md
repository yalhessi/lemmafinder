Coq Lemma Synthesis Plugin
---------------------------

Software Versions:

- Dune 2.7
- Coq 8.11

## How to build and install

```
$ dune build
```

```
$ dune install
```


and the rest of regular Dune commands, to test your library, you can use

```
$ dune exec -- coqtop -R _build/default/theories lfind
```


