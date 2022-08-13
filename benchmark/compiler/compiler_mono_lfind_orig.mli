
val add : nat -> nat -> nat

type exp =
| Num of nat
| Plus of exp * exp

type listnat =
| Natnil
| Natcons of nat * listnat

val evalExp : exp -> nat

type instr =
| Push of nat
| Add

type listinstr =
| Instrnil
| Instrcons of instr * listinstr

val instrapp : listinstr -> listinstr -> listinstr

val execI : instr -> listnat -> listnat

val execIs : listinstr -> listnat -> listnat

val compile : exp -> listinstr
