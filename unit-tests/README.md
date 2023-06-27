# Instructions to Run Unit Test
You'll need to have `OUnit2` installed, to do this run: `opam install ounit2`. You should also have `lfind` installed via instructions listed in this repo (instructions in `../lemmafinder/README.md`).

Then run the following commands:
1. `$ cd ../lemmafinder/unit-tests`
2. `$ dune build`
3. `$ dune exec ./Utests.exe`
4. This should run the unit tests using OCaml's module **OUnit2**

## Tests Currently Include:
- LFIND path is set
- Prover path is set
- End to end test (using LFind as user would) for `list_rev.v`(calling `lfind` within theorem `rev_rev` in place of lemma `rev_append`)
  - Commented out because it is not a unit test
- Generalization test (with `Generalize_NoDup.construct_all_generalizations` as the function being tested)
  - Uses `motivating_example/list_rev.v` to get the inputs and expected outputs from the function
- Conjecture creation test (with `Generalize_NoDup.get_all_conjectures` as the function being tested)
  - Uses `motivating_example/list_rev.v` to get the inputs and expected outputs from the function
