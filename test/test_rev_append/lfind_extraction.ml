
type listnat =
| Natnil
| Natcons of nat * listnat

(** val lfind_example_y : listnat **)

let lfind_example_y =
  Natcons ((S (O)), Natnil)

(** val lfind_example_x : listnat **)

let lfind_example_x =
  Natnil
