Load LFindLoad.
From lfind Require Import LFind.
Unset Printing Notations.
Set Printing Implicit.


Inductive lst : Type :=
  | Nil : lst
  | Cons : nat -> lst -> lst.

Fixpoint lf_append (l1 : lst) (l2 : lst) : lst :=
  match l1 with
  | Nil => l2
  | Cons x y => Cons x (lf_append y l2)
  end.

Fixpoint rev (l : lst) : lst :=
  match l with
  | Nil => Nil
  | Cons x y => lf_append (rev y) (Cons x Nil)
  end.

Lemma append_nil : forall x : lst, lf_append x Nil = x.
Proof.
  intros.
  induction x.
  - reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.

Lemma append_assoc : forall x y z : lst,
lf_append x (lf_append y z) = lf_append (lf_append x y) z.
Proof.
  intros.
  induction x.
  - reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.

Lemma rev_append: forall x y : lst, rev (lf_append x y) = lf_append (rev y) (rev x).
Proof.
  intros.
  induction x.
  - simpl. rewrite append_nil. reflexivity.
  - simpl. rewrite IHx. rewrite append_assoc. reflexivity.
Qed.

Theorem rev_rev : forall x : lst, rev (rev x) = x.
Proof.
  intros.
  induction x.
  - reflexivity.
  - simpl. 
  lfind_debug.
  Admitted.
  (* rewrite rev_append. rewrite IHx. reflexivity.
Qed. *)
