
type natural =
| Z
| P of natural

(** val add : natural -> natural -> natural **)

let rec add n m =
  match n with
  | Z -> m
  | P p -> P (add p m)

type exp =
| Num of natural
| Plus of exp * exp

type listnat =
| Natnil
| Natcons of natural * listnat

(** val evalExp : exp -> natural **)

let rec evalExp = function
| Num n -> n
| Plus (e1, e2) -> add (evalExp e1) (evalExp e2)

type instr =
| Push of natural
| Add

type listinstr =
| Instrnil
| Instrcons of instr * listinstr

(** val instrapp : listinstr -> listinstr -> listinstr **)

let rec instrapp l m =
  match l with
  | Instrnil -> m
  | Instrcons (a, l1) -> Instrcons (a, (instrapp l1 m))

(** val execI : instr -> listnat -> listnat **)

let execI i s =
  match i with
  | Push n -> Natcons (n, s)
  | Add ->
    (match s with
     | Natnil -> Natnil
     | Natcons (n1, l) ->
       (match l with
        | Natnil -> Natnil
        | Natcons (n2, rest) -> Natcons ((add n1 n2), rest)))

(** val execIs : listinstr -> listnat -> listnat **)

let rec execIs l s =
  match l with
  | Instrnil -> s
  | Instrcons (i, is) -> execIs is (execI i s)

(** val compile : exp -> listinstr **)

let rec compile = function
| Num n -> Instrcons ((Push (n)), Instrnil)
| Plus (e1, e2) ->
  instrapp (compile e2) (instrapp (compile e1) (Instrcons (Add, Instrnil)))
