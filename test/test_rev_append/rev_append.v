Unset Printing Notations.
Set Printing Implicit.

Inductive listnat : Type :=
  | Natnil : listnat
  | Natcons : nat -> listnat -> listnat.

Fixpoint app (l : listnat) (m: listnat): listnat :=
match l with
  | Natnil => m
  | Natcons a l1 => Natcons a (app l1 m)
end.

Fixpoint rev (l:listnat): listnat :=
  match l with
  | Natnil => Natnil
  | Natcons a l1 => app (rev l1) (Natcons a Natnil)
  end. 

Theorem app_nil_r (l:listnat) : app l Natnil = l.
Proof.
  intros.
  induction l.
  -simpl. reflexivity.
  -simpl. rewrite IHl. reflexivity.
Qed.

Theorem rev_append: forall x y: listnat, (eq (rev (app x y)) (app (rev y) (rev x))).
Proof.
  intros.
    induction x.
    - simpl. rewrite app_nil_r. reflexivity.
    - simpl. rewrite IHx.
Admitted.