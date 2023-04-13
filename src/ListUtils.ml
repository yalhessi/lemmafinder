let split list n =
  let rec aux i acc = function
    | [] -> List.rev acc, []
    | h :: t as l -> if i = 0 then List.rev acc, l
                     else aux (i - 1) (h :: acc) t 
  in
    aux n [] list

let findi (f : (int -> 'a -> bool)) (l : 'a list) : int*'a =
  let rec findi' n l = match l with
    | [] -> raise Not_found
    | x :: _ when f n x -> (n, x)
    | _ :: l -> findi' (n + 1) l
  in findi' 0 l

let[@tail_mod_cons] rec filter_map f = function
  | [] -> []
  | x :: l ->
      match f x with
      | None -> filter_map f l
      | Some v -> v :: filter_map f l