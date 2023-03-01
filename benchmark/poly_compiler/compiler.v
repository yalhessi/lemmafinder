Require Import Coq.Lists.List.

Inductive exp : Type :=
| Num : nat -> exp
| Plus : exp -> exp -> exp.

Fixpoint evalExp (e : exp) : nat :=
  match e with
  | Num n => n
  | Plus e1 e2 => 
   (evalExp e1) + (evalExp e2)
  end
.

Inductive instr : Type :=
| Push : nat -> instr
| AddI : instr.

Definition execI 
  (i : instr) (s : list nat) : list nat :=
  match i with
  | Push n => (n :: s)
  | AddI =>
    match s with
    | (n1 :: (n2 :: rest)) => (n1 + n2) :: rest
    | _ => nil
    end
  end.

Fixpoint execIs 
  (l : list instr) (s : list nat) : list nat :=
  match l with
  | nil => s
  | i :: is => execIs is (execI i s)
  end.

Fixpoint compile (e : exp) : list instr :=
  match e with
  | Num n => (Push n) :: nil
  | Plus e1 e2 => 
  (compile e2) ++ (compile e1) ++ (AddI :: nil)
  end.

Lemma correct_compilation_strong:
forall  (e : exp) (l : list instr) (s: list nat), (@eq (list nat) (execIs ((compile e) ++ l) s) (execIs l (cons (evalExp e) s))).
Proof.
induction e.
- intros. reflexivity.
- intros. simpl. rewrite <- List.app_assoc. rewrite IHe2. rewrite <- List.app_assoc. rewrite IHe1. simpl. reflexivity.
Qed.
  
Theorem correct_compilation:
forall e,
(execIs (compile e) nil) =
(cons (evalExp e) nil).
Proof.
  intros.
  induction e.
  - simpl. reflexivity.
  - simpl. rewrite correct_compilation_strong.
    rewrite correct_compilation_strong. auto.
Qed.
