Load LFindLoad.
From lfind Require Import LFind.
Unset Printing Notations.
Set Printing Implicit.

From QuickChick Require Import QuickChick Tactics.

(* GOAL : set up theorems that try to synthesize theorems from Coq arithmetic library *)

Inductive allZero : list nat -> Prop :=
| zero_e : forall l, l = nil -> allZero l
| zero_f : forall h t, (h = 0) /\ (allZero t) -> (allZero (h :: t)).

Instance allZero_dec (lst : list nat) : Dec (allZero lst).
Proof.
    constructor.
    dec_eq.
    induction lst. 
    -   left.
        apply zero_e.
        reflexivity.
    -   destruct IHlst.
        + destruct a. 
            ++ left. apply zero_f. split. reflexivity. apply a0.
            ++ right. unfold not. intros. inversion H. 
            +++ discriminate H0.
            +++ destruct H1. discriminate H1.
        + right. unfold not. intros. inversion H.
            ++ discriminate H0.
            ++ destruct H1. apply n. apply H3.
Qed. 

Inductive containsZero : list nat -> Prop :=
| has_zero : forall h t, (h = 0) \/ (containsZero t) -> (containsZero (h :: t)).

Lemma contains_zero_simp : forall a l, containsZero l -> containsZero (a :: l).
Proof.
    intros. apply has_zero. right. apply H.
Qed.

Instance containsZero_dec (lst : list nat) : Dec (containsZero lst).
Proof.
    constructor. dec_eq.
    induction lst.
    - right. unfold not. intros. inversion H.
    - destruct a.
    + left. apply has_zero. left. reflexivity.
    + destruct IHlst.
    ++ left. apply has_zero. right. apply c.
    ++ right. unfold not. intros. unfold not in n. apply n. inversion H.
    destruct H1.
    * discriminate H1.
    * apply H1.
Qed.

Lemma In_0_containsZero : forall l, containsZero l <-> Coq.Lists.List.In 0 l.
Proof.
    split.
    + intro. induction l.
    - simpl. inversion H.
    - destruct a. 
    -- simpl. left. reflexivity.
    -- simpl. right. apply IHl. inversion H. destruct H1.
    --- discriminate H1.
    --- apply H1.
    + intro. induction l.
    - contradiction H.
    - apply has_zero. destruct a.
    -- left. reflexivity.
    -- right. apply IHl. inversion H.
    --- discriminate H0.
    --- apply H0.
Qed.    

Fixpoint listSum (lst : list nat) : nat :=
    match lst with
    | nil => 0
    | cons h t => h + (listSum t)
end.

Fixpoint listProduct (lst : list nat) : nat :=
    match lst with
    | nil => 1
    | cons h t => h * (listProduct t)
end.

Lemma sum_list_zero : forall lst, allZero lst -> listSum lst = 0.
Proof.
    intros lst. induction lst.
    - intros. reflexivity.
    - intros. simpl. destruct a. 
    -- simpl. inversion H.
    --- discriminate H0.
    --- destruct H1. apply IHlst. apply H3.
    -- inversion H. discriminate H0. destruct H1. discriminate H1.
Qed.

(* Uses helper lemma: 
    - Coq.Arith.Mult.mult_0_r *)
Lemma product_list_zero : forall lst, containsZero lst -> listProduct lst = 0.
Proof.
    intros. induction lst.
    - inversion H.
    - simpl. inversion H. destruct H1.
    -- rewrite H1. reflexivity.
    -- apply IHlst in H1. rewrite H1. apply Coq.Arith.Mult.mult_0_r.
Qed.

(* Uses helper lemmas: 
    - Coq.Arith.Plus.le_plus_r *)
Theorem sum_list_incr_weaker : forall a lst, listSum lst <= listSum (a :: lst).
Proof.
    intros. simpl. apply Coq.Arith.Plus.le_plus_r.
Qed.

(* Commented out uses helper lemmas: 
    - Coq.Arith.Lt.lt_irrefl
    - Coq.Arith.Lt.le_lt_n_Sm
    - Coq.Arith.Plus.le_plus_r *)
(* Uses helper lemmas: 
    - Coq.Arith.Lt.lt_S_n
    - Coq.Arith.Lt.le_lt_n_Sm
    - Coq.Arith.Le.le_n_S 
    - sum_list_incr_weaker <defined above> *)
Theorem sum_list_incr : forall a lst, 0 < a -> listSum lst < listSum (a :: lst).
Proof.
    (* intros. simpl. destruct a.
    - apply Coq.Arith.Lt.lt_irrefl in H. 
    contradiction H.
    - simpl. apply Coq.Arith.Lt.le_lt_n_Sm. 
    apply Coq.Arith.Plus.le_plus_r. *)
    intros. apply Coq.Arith.Lt.lt_S_n. 
    apply Coq.Arith.Lt.le_lt_n_Sm.  destruct a.
    - inversion H.
    - simpl. apply Coq.Arith.Le.le_n_S. apply sum_list_incr_weaker. 
Qed.

(* Uses helper lemmas:
    - Coq.Arith.Plus.plus_0_r
    - Coq.Arith.Plus.le_plus_l
    - Coq.Arith.Plus.le_plus_r <commutativity of previous lemma> *)
Theorem prod_list_incr : forall a lst, 1 < a  -> listProduct lst <= listProduct (a :: lst).
Proof.
    intros. inversion H.
    - simpl. rewrite Coq.Arith.Plus.plus_0_r. apply Coq.Arith.Plus.le_plus_r.
    - simpl. 
    (* invoke lfind here *)
    lfind_debug. 
    Admitted.
    (* apply Coq.Arith.Plus.le_plus_l.
Qed. *)