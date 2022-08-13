
type natural =
| Z
| P of natural

val add : natural -> natural -> natural

type exp =
| Num of natural
| Plus of exp * exp

type listnat =
| Natnil
| Natcons of natural * listnat

val evalExp : exp -> natural

type instr =
| Push of natural
| Add

type listinstr =
| Instrnil
| Instrcons of instr * listinstr

val instrapp : listinstr -> listinstr -> listinstr

val execI : instr -> listnat -> listnat

val execIs : listinstr -> listnat -> listnat

val compile : exp -> listinstr
