From lfind Require Import LFind.
Unset Printing Notations.
Set Printing Implicit.
From QuickChick Require Import QuickChick.
QCInclude ".".
Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".
Require Coq.extraction.Extraction.
Extraction Language OCaml.


Inductive listnat : Type :=
  | Natnil : listnat
  | Natcons : nat -> listnat -> listnat.

Derive Show for listnat.
Derive Arbitrary for listnat.
Instance Dec_Eq_listnat : Dec_Eq listnat.
Proof. dec_eq. Qed.

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
    - simpl. rewrite IHx. lfind.
    (* lfind. *)
Admitted.
(* Proof.
  induction x.
  {
    simpl.
    intros.
    destruct y.
    {
      eauto.
    }
    {
      auto with *.
    }
  }
  {
    simpl.
    intros.
    rewrite IHx.
    destruct y.
    {
      eauto.
    }
    {
      auto with *.
    }
  }
Qed. *)
(* Proof.
  induction x.
  {
    simpl.
    intros.
    destruct y.
    {
      eauto.
    }
    {
      intuition.
    }
  }
  {
    simpl.
    intros.
    rewrite IHx.
    destruct y.
    {
      eauto.
    }
    {
      intuition.
    }
  }
    (* induction x.
    simpl.
    intros.
    destruct y.
    eauto.
    intuition.
    simpl.
    intros.
    rewrite IHx.
    destruct y.
    eauto.
    intuition. *)
    (* Qed.
    intros.
    induction x.
    - simpl. rewrite app_nil_r. reflexivity.
    - simpl. rewrite IHx. lfind. *)
Qed. *)

(* Extraction "rev_append.ml" rev app list nat. *)

(* 
Lemma gen_examples : forall (x y: listnat) (n: nat), 
rev (app x y) = app (rev y) (rev x) ->
app (app (rev y) (rev x)) (Natcons n Natnil) =
app (rev y) (app (rev x) (Natcons n Natnil)).
Admitted.

Open Scope string_scope.
Parameter print : listnat -> string -> listnat.
Extract Constant print => "Extract.print".

Definition collect_data (x:listnat) (y:listnat) (a: nat) := 
  let x_str := "x:" ++ "(" ++ show x ++ ")"
  in let y_str := x_str ++ "|" ++ "y:" ++ "(" ++ show y ++ ")"
  in let a_str := y_str ++ "|" ++ "n:" ++ "(" ++ show a ++ ")"
  in let x_1 := print x a_str
  in gen_examples x_1 y a.

QuickChick collect_data. *)