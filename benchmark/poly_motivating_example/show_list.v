Require Import String. Open Scope string.
Instance show_list {T} `{_ : Show T} : Show (list T) := 
{| show := 
     let fix aux l :=
       match l with
       | nil => "@nil nat"
       | cons x xs => "@cons nat " ++ show x ++ " (" ++ aux xs ++ ")"
       end
      in aux
|}.
Derive Arbitrary for list.
Instance Dec_Eq_list : Dec_Eq (list nat).
Proof. dec_eq. Qed.
