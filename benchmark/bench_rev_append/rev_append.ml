type nat =
  | O
  | S of nat

type listnat =
  | Natnil
  | Natcons of nat * listnat
  

  
  let rec app (l:listnat) (m:listnat) : listnat =
    match l with
    | Natnil -> m
    | Natcons (a, l1) -> Natcons (a, (app l1 m))
  
 ;;
  
  let rec rev (l:listnat) : listnat = 
    match l with
  | Natnil -> Natnil
  | Natcons (a, l1) -> app (rev l1) (Natcons (a, Natnil))
  ;;
