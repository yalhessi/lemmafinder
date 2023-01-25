type coqtype =
  | Basic of string
  | Abstract of string
  | Parametric of string * coqtype list

(* let string_to_coqtype typ_name typ_type = if String.equal typ_type "Type" then Parametric typ_name
else if String.contains typ_name ' ' then Parametric (typ_name, [Basic typ_type]

) else *)
