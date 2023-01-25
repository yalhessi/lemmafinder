(** This module is a very simple parsing library for S-expressions. *)

(* Copyright (C) 2009  Florent Monnier, released under MIT license. *)
(* modified to match the task description *)

type t = Atom of string | Expr of t list

type state =
  | Parse_root of t list
  | Parse_content of t list
  | Parse_word of Buffer.t * t list
  | Parse_string of bool * Buffer.t * t list

let parse pop_char =
  let rec aux st =
    match pop_char () with
    | None -> (
        match st with
        | Parse_root sl -> List.rev sl
        | Parse_content _ | Parse_word _ | Parse_string _ ->
            failwith "Parsing error: content not closed by parenthesis" )
    | Some c -> (
        match c with
        | '(' -> (
            match st with
            | Parse_root sl ->
                let this = aux (Parse_content []) in
                aux (Parse_root (Expr this :: sl))
            | Parse_content sl ->
                let this = aux (Parse_content []) in
                aux (Parse_content (Expr this :: sl))
            | Parse_word (w, sl) ->
                let this = aux (Parse_content []) in
                aux
                  (Parse_content (Expr this :: Atom (Buffer.contents w) :: sl))
            | Parse_string (_, s, sl) ->
                Buffer.add_char s c;
                aux (Parse_string (false, s, sl)) )
        | ')' -> (
            match st with
            | Parse_root sl ->
                failwith "Parsing error: closing parenthesis without openning"
            | Parse_content sl -> List.rev sl
            | Parse_word (w, sl) -> List.rev (Atom (Buffer.contents w) :: sl)
            | Parse_string (_, s, sl) ->
                Buffer.add_char s c;
                aux (Parse_string (false, s, sl)) )
        | ' ' | '\n' | '\r' | '\t' -> (
            match st with
            | Parse_root sl -> aux (Parse_root sl)
            | Parse_content sl -> aux (Parse_content sl)
            | Parse_word (w, sl) ->
                aux (Parse_content (Atom (Buffer.contents w) :: sl))
            | Parse_string (_, s, sl) ->
                Buffer.add_char s c;
                aux (Parse_string (false, s, sl)) )
        | '"' -> (
            (* '"' *)
            match st with
            | Parse_root _ -> failwith "Parse error: double quote at root level"
            | Parse_content sl ->
                let s = Buffer.create 74 in
                aux (Parse_string (false, s, sl))
            | Parse_word (w, sl) ->
                let s = Buffer.create 74 in
                aux (Parse_string (false, s, Atom (Buffer.contents w) :: sl))
            | Parse_string (true, s, sl) ->
                Buffer.add_char s c;
                aux (Parse_string (false, s, sl))
            | Parse_string (false, s, sl) ->
                aux (Parse_content (Atom (Buffer.contents s) :: sl)) )
        | '\\' -> (
            match st with
            | Parse_string (true, s, sl) ->
                Buffer.add_char s c;
                aux (Parse_string (false, s, sl))
            | Parse_string (false, s, sl) -> aux (Parse_string (true, s, sl))
            | _ -> failwith "Parsing error: escape character in wrong place" )
        | _ -> (
            match st with
            | Parse_root _ ->
                failwith
                  (Printf.sprintf "Parsing error: char '%c' at root level" c)
            | Parse_content sl ->
                let w = Buffer.create 16 in
                Buffer.add_char w c;
                aux (Parse_word (w, sl))
            | Parse_word (w, sl) ->
                Buffer.add_char w c;
                aux (Parse_word (w, sl))
            | Parse_string (_, s, sl) ->
                Buffer.add_char s c;
                aux (Parse_string (false, s, sl)) ) )
  in
  aux (Parse_root [])

let string_pop_char str =
  let len = String.length str in
  let i = ref (-1) in
  function
  | () ->
      incr i;
      if !i >= len then None else Some str.[!i]

let of_string str = parse (string_pop_char str)

let ic_pop_char ic = function
  | () -> ( try Some (input_char ic) with End_of_file -> None )

let parse_ic ic = parse (ic_pop_char ic)

let parse_file filename =
  let ic = open_in filename in
  let res = parse_ic ic in
  close_in ic;
  res

let quote s = "\"" ^ s ^ "\""

let needs_quote s =
  List.exists (String.contains s) [ ' '; '\n'; '\r'; '\t'; '('; ')' ]

let protect s =
  let s = String.escaped s in
  if needs_quote s then quote s else s

let string_of_sexpr s =
  let rec aux acc = function
    | Atom tag :: tl -> aux (protect tag :: acc) tl
    | Expr e :: tl ->
        let s = "(" ^ String.concat " " (aux [] e) ^ ")" in
        aux (s :: acc) tl
    | [] -> List.rev acc
  in
  String.concat " " (aux [] s)

let print_sexpr s = print_endline (string_of_sexpr s)

let string_of_sexpr_indent s =
  let rec aux i acc = function
    | Atom tag :: tl -> aux i (protect tag :: acc) tl
    | Expr e :: tl ->
        let s =
          "\n" ^ String.make i ' ' ^ "("
          ^ String.concat " " (aux (succ i) [] e)
          ^ ")"
        in
        aux i (s :: acc) tl
    | [] -> List.rev acc
  in
  String.concat "\n" (aux 0 [] s)

let get_normalized_var_name count = "lv" ^ string_of_int count

let normalize_sexp s (orig_var_types : (string, string) Hashtbl.t) =
  let normalized_var_map = Hashtbl.create (Hashtbl.length orig_var_types) in
  let count = ref 0 in
  let rec aux (i : int) (acc, orig_vars) = function
    | Atom tag :: tl -> (
        try
          let _ = Hashtbl.find normalized_var_map tag in
          aux i (acc, orig_vars) tl
        with _ -> (
          try
            let v = Hashtbl.find orig_var_types tag in
            let new_var = get_normalized_var_name !count in
            count := !count + 1;
            Hashtbl.add normalized_var_map tag new_var;
            let new_acc =
              if String.equal tag Consts.synthesis_op then (acc, orig_vars)
              else
                ( acc ^ " " ^ "(" ^ new_var ^ " : " ^ v ^ ")",
                  List.append orig_vars [ tag ] )
            in
            aux i new_acc tl
          with _ -> aux i (acc, orig_vars) tl ) )
    | Expr e :: tl ->
        let head_acc, head_orig_vars = aux (succ i) (acc, orig_vars) e in
        aux i (head_acc, head_orig_vars) tl
    | [] -> (acc, orig_vars)
  in
  let vars_str, orig_vars = aux 0 ("", []) s in
  (vars_str, orig_vars, normalized_var_map)

let normalize_sexp_vars s normalized_vars =
  let rec aux i acc = function
    | Atom tag :: tl ->
        let t = try Hashtbl.find normalized_vars tag with _ -> protect tag in
        aux i (t :: acc) tl
    | Expr e :: tl ->
        let s = "(" ^ String.concat " " (aux (succ i) [] e) ^ ")" in
        aux i (s :: acc) tl
    | [] -> List.rev acc
  in
  String.concat "\n" (aux 0 [] s)

let print_sexpr_indent s = print_endline (string_of_sexpr_indent s)

let equal e1 e2 =
  let e1_str = string_of_sexpr e1 in
  let e2_str = string_of_sexpr e2 in
  String.equal e1_str e2_str

let size sexp = String.length (string_of_sexpr sexp)

let sexp_size sexp =
  let rec aux acc = function
    | Atom tag :: tl -> aux (acc + 1) tl
    | Expr e :: tl ->
        let s = aux 0 e in
        aux (s + acc) tl
    | [] -> acc
  in
  aux 0 sexp

let replace_sub_sexp sexp sub_expr repl_expr =
  let rec aux (acc : string list) = function
    | Atom tag :: tl ->
        let to_app =
          if equal [ Atom tag ] sub_expr then "(" ^ repl_expr ^ ")"
          else protect tag
        in
        aux (to_app :: acc) tl
    | Expr e :: tl ->
        let str_to_concat = aux [] e in
        let to_app =
          if equal e sub_expr then "(" ^ repl_expr ^ ")"
          else "(" ^ String.concat " " str_to_concat ^ ")"
        in
        aux (to_app :: acc) tl
    | [] -> List.rev acc
  in
  let str_expr = aux [] sexp in
  String.concat " " str_expr
