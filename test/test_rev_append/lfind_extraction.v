
 From test Require Import rev_append.
 
 Require Import Extraction.
 Extract Inductive nat => nat [ "(O)" "S" ].
 Extract Inductive list => list [ "Nil" "Cons" ].
Definition lfind_example_y  := (Natcons 1 Natnil).
Definition lfind_example_x  := (Natnil).

 
                    Extraction "/Users/aish/Documents/lemmafinder/test/test_rev_append/lfind_extraction.ml" lfind_example_y lfind_example_x .