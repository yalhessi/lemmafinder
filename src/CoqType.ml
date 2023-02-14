type coqtype =
  | Concrete of string
  | TypeVar of string
  | Parametric of string * coqtype list
  | Type

type coqvartype = Vartype of string * coqtype

(* TODO: this should be a set but in older ocaml, that's a bit more work *)
let type_vars = ref []

let string_to_coqtype typ =
  if List.mem typ !type_vars then TypeVar typ else Concrete typ

let remove_last_char str = String.sub str 0 (String.length str - 1)

let remove_first_char str = String.sub str 1 (String.length str - 1)

let extract_typ_from_var_typ var_typ : string =
  String.split_on_char ':' var_typ |> List.tl |> List.hd |> remove_last_char

let extract_var_from_var_typ var_typ : string =
  String.split_on_char ':' var_typ |> List.hd |> remove_first_char

let split_var_typ var_typ : string * string =
  (extract_var_from_var_typ var_typ, extract_typ_from_var_typ var_typ)
let string_to_coqvartype typed_var =
  let var_name, var_type = split_var_typ typed_var in
  print_endline ("var_name: " ^ var_name ^ " var_type: " ^ var_type);
  if List.mem var_type !type_vars then Vartype (var_name, TypeVar var_type)
  else if String.equal var_type "Type" then (
    if not (List.mem var_name !type_vars) then
      type_vars := var_name :: !type_vars;
    Vartype (var_name, Type) )
  else if String.contains var_type ' ' then
    (* TODO: this probably needs better parsing for nested parametric types *)
    let parsed_var_type = String.split_on_char ' ' var_type in
    Vartype
      ( var_name,
        Parametric
          ( List.hd parsed_var_type,
            List.map string_to_coqtype (List.tl parsed_var_type) ) )
  else Vartype (var_name, Concrete var_type)

let rec debug_coqtype_to_string typ =
  match typ with
  | Concrete s -> "Basic" ^ s
  | TypeVar s -> "Abstract" ^ s
  | Parametric (s, params) ->
      "Parametric" ^ s ^ "("
      ^ String.concat ", " (List.map debug_coqtype_to_string params)
      ^ ")"
  | Type -> "Type"


let rec coqtype_to_string typ =
  match typ with
  | Concrete s -> s
  | TypeVar s -> s
  | Parametric (s, params) ->
      s ^ "("
      ^ String.concat ", " (List.map coqtype_to_string params)
      ^ ")"
  | Type -> "Type"

let get_type_name typ = 
  match typ with
  | Concrete s -> s
  | TypeVar s -> s
  | Parametric (s, _) -> s
  | Type -> "Type"
  
let coqvartype_to_string (Vartype (var_name, var_type)) =
  "(" ^ var_name ^ ": " ^ coqtype_to_string var_type ^ ")"



