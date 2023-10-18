type t = 
{
  label : string;
  params : (string * string) list;
  output_type : EConstr.t;
  examples : (string * string) list; (* (inp1,inp2,...,inpn),output *)
}

let same_problems (context : LFContext.t) (a : t) (b : t) : bool =
  let compare_types = String.equal (LFContext.e_str context a.output_type) (LFContext.e_str context b.output_type) in
  let compare_paired_list x y = 
    match (List.length x) == (List.length y) with
    | true -> List.fold_left2 ( fun eq (x1,x2) (y1,y2) -> (String.equal x1 y1) && (String.equal x2 y2) && eq ) true x y
    | _ -> false in
  let compare_params = compare_paired_list a.params b.params in
  let compare_examples = compare_paired_list a.examples b.examples in
  compare_types && compare_examples && compare_params

let get_input_examples (params : (string * string) list) (example : (string,string) Hashtbl.t) : string =
  let fetch_param var = 
    try Hashtbl.find example var
    with _ -> ("nat") in (* This is hard coded... assuming if general type is used/not found, then it is nat [might be wrong]*)
  let values = List.map (fun (v,_) -> fetch_param v) params in
  if List.mem "" values then "" else String.concat "," values 

let generate_examples (context : LFContext.t) (sketch : Sketch.t) (params : (string * string) list)
(generalized : (string, Evd.econstr * Names.variable * Evd.econstr) Hashtbl.t)
(original_examples : (string, string) Hashtbl.t list) : (string * string) list =
  let per_example ex =
    match Evaluate.econstr_term_with_vars context generalized ex sketch.hole with 
    | Some output -> ((get_input_examples params ex),output)
    | None -> 
      raise (Failure ("Failed to generate example output for synthesizer (triggered in Synthesis.ml). 
      \nFailed on input: " ^ (Hashtbl.fold (fun x y acc -> acc ^ "\n" ^ x ^ " : " ^ y) ex "")))
  in List.map per_example original_examples

let get_full_type (context : LFContext.t) (typ : EConstr.t) : string =
  match (Utils.get_func_str_with_mod context.env context.sigma typ) with 
  | "" -> LFContext.e_str context typ
  | typ_string -> typ_string

let get_query_params (context : LFContext.t) (sketch : Sketch.t) : (string * string) list =
  Hashtbl.fold
  (
    fun var_str (typ,var,term) accum -> 
      if Constr.is_Type (EConstr.to_constr context.sigma typ) 
      then (var_str,(LFContext.e_str context typ)) :: accum (* listing the types first *)
      else accum @ [(var_str,(get_full_type context typ))]
  ) sketch.variables []

let problem_from_sketch (context : LFContext.t) (sketch : Sketch.t) (generalized : (string, Evd.econstr * Names.variable * Evd.econstr) Hashtbl.t)
(original_examples : (string, string) Hashtbl.t list) : t = 
  let params = get_query_params context sketch in
  let examples = generate_examples context sketch params generalized original_examples in
  { label = ""; params; output_type = sketch.hole_type; examples } 

let create_problems (context : LFContext.t) (sketches : Sketch.t list) (generalized : (string, Evd.econstr * Names.variable * Evd.econstr) Hashtbl.t)
(examples : (string, string) Hashtbl.t list) : t list * (string, string) Hashtbl.t =
  let sketch_record = Hashtbl.create (List.length sketches) in
  let rec iter index accum = function
  | [] -> accum
  | (sketch : Sketch.t) :: remaining ->
    let problem = problem_from_sketch context sketch generalized examples in
    match Utils.find_in_list (same_problems context) problem accum with
    | Some p -> Hashtbl.add sketch_record sketch.label p.label; iter index accum remaining
    | None -> let label = Consts.fmt "synth_%d" index in
        Hashtbl.add sketch_record sketch.label label; iter (index + 1) (accum @ [{problem with label}]) remaining in
  (iter 1 [] sketches),sketch_record

