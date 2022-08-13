
type natural =
  | Z
  | P of natural
  
  type exp =
    | Num of natural
    | Plus of exp * exp
    
  type listnat =
  | Natnil
  | Natcons of natural * listnat
  
  type instr =
    | Push of natural
    | Add
    
    type listinstr =
    | Instrnil
    | Instrcons of instr * listinstr
  
  let rec add (n: natural) (m:natural) : natural =
  match n with
  | Z -> m
  | P p -> P (add p m)
  ;;
    
  let rec evalExp (e: exp) : natural = 
  match e with
  | Num n -> n
  | Plus (e1, e2) -> add (evalExp e1) (evalExp e2)
  
  ;;
  let rec instrapp (l:listinstr) (m:listinstr) : listinstr=
    match l with
    | Instrnil -> m
    | Instrcons (a, l1) -> Instrcons (a, (instrapp l1 m))
  ;;
  
  let execI (i:instr) (s: listnat) : listnat =
    match i with
    | Push n -> Natcons (n, s)
    | Add ->
      (match s with
       | Natnil -> Natnil
       | Natcons (n1, l) ->
         (match l with
          | Natnil -> Natnil
          | Natcons (n2, rest) -> Natcons ((add n1 n2), rest)))
  ;;
  
  let rec execIs (l:listinstr) (s:listnat) :listnat =
    match l with
    | Instrnil -> s
    | Instrcons (i, is) -> execIs is (execI i s)
  
  ;;
  
  let rec compile (e: exp) : listinstr = 
    match e with 
  | Num n -> Instrcons ((Push (n)), Instrnil)
  | Plus (e1, e2) ->
    instrapp (compile e2) (instrapp (compile e1) (Instrcons (Add, Instrnil)))
  ;;
