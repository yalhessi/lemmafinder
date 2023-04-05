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
- End to end test (using LFind as user would) for `list_rev.ml`(calling `lfind` within theorem `rev_rev` in place of lemma `rev_append`)
  - Determine success of test by if the number of synthesized lemmas match _exactly_ (might want to weaken this test depending on running time)
- **_todo_** : potentially more end to end tests (might not be necessary)
  - _potentially_  include better failure messages for end to end test, although once the unit tests are included for the incrementaly behavior this wouldn't really be necessary
- **_todo_** : once code is modularized and clean-up incorporate unit tests within the body of `lfind` to incrementally test behavior
