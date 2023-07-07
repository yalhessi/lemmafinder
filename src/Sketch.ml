type t =
{
  label : string;
  goal : EConstr.t;
  goal_with_hole : EConstr.t;
  hole : EConstr.t;
  hole_type : EConstr.t;
  variables : (string, (EConstr.t * Names.variable * EConstr.t)) Hashtbl.t; (* string , (type,var,term) *)
}

let rec get_var_outside_of_hole (context : LFContext.t) (generalization : Generalization.t) (goal_with_hole : EConstr.t) : Names.variable list =
  match Constr.kind (EConstr.to_constr context.sigma goal_with_hole) with
  | Var id -> if (String.equal "(##hole##)" (Names.Id.to_string id)) then [] else [id]
  | App (_, args) -> 
    (
      let args_list =  List.map EConstr.of_constr (Array.to_list args) in 
      List.flatten(List.map (get_var_outside_of_hole context generalization) args_list)
    )
  | Prod (_,hypo,result) -> (* Prod is the implication type, not including variable bindings below *)
    (
      let args_list =  List.map EConstr.of_constr [hypo;result] in 
      List.flatten(List.map (get_var_outside_of_hole context generalization) args_list)
    )
  | Lambda (_,inp,body) -> 
    (
      let args_list =  List.map EConstr.of_constr [inp;body] in 
      List.flatten(List.map (get_var_outside_of_hole context generalization) args_list)
    )
  | LetIn (_,inp,assignment,expr) ->
    (
      let args_list =  List.map EConstr.of_constr [inp;assignment;expr] in 
      List.flatten (List.map (get_var_outside_of_hole context generalization) args_list)
    )
  | Case (_,a,b,arr) -> 
    (
      let args_list =  List.map EConstr.of_constr ([a;b] @ (Array.to_list arr)) in 
      List.flatten(List.map (get_var_outside_of_hole context generalization) args_list)
    )
  | Int _ | Float _ | Const (_,_) | Construct (_,_) | Sort _ | Rel _ | Meta _ | Ind (_,_) -> []
  | _ -> print_endline ("Constr = " ^ (LFContext.e_str context goal_with_hole));
    raise (Failure "Constr match not handled for finding variables outside of hole (triggered in Sketch.ml)")

let sketch_variable_tbl (generalization : Generalization.t) (variables : Names.variable list) 
: (string, (EConstr.t * Names.variable * EConstr.t)) Hashtbl.t = 
  let var_eq a b = String.equal (Names.Id.to_string a) (Names.Id.to_string b) in
  let result = Hashtbl.create (List.length variables) in 
  let get_info var = 
    let var_str = Names.Id.to_string var in
    let value = try Hashtbl.find generalization.variables var_str 
    with _-> raise (Failure "Variable not found in generalization variable table (triggered in Sketch.ml)") in
    Hashtbl.add result var_str value in
  List.iter get_info (Utils.remove_duplicates var_eq variables); result

let create_subterm_sketch (context : LFContext.t) (generalization : Generalization.t)
(hole_str : string) (info_tuple : (Evd.econstr * Evd.econstr * int)) (sketches : t list) : t list = 
  match Hashtbl.mem generalization.variables hole_str with 
  | true -> sketches
  | false ->
    (
      let hole,typ_econstr,label_num = info_tuple in
      let label = Consts.fmt "%s_term_sketch%d" generalization.label label_num in
      let to_constr = EConstr.to_constr context.sigma in
      let goal_with_hole = EConstr.of_constr (LFCoq.make_equal_to_str (to_constr typ_econstr) (to_constr hole) "(##hole##)") in
      let var_list = get_var_outside_of_hole context generalization goal_with_hole in
      let variables = sketch_variable_tbl generalization var_list in
      { label; goal = generalization.goal; goal_with_hole; hole; hole_type = typ_econstr; variables; } :: sketches
    )

let create_sketch (context : LFContext.t) (generalization : Generalization.t)
(hole_str : string) (info_tuple : (Evd.econstr * Evd.econstr * int)) (sketches : t list) : t list = 
  let hole,typ_econstr,label_num = info_tuple in
  let label = Consts.fmt "%s_sketch%d" generalization.label label_num in
  let goal_with_hole = ExampleManagement.replace_var_with_value context hole_str "##hole##" generalization.goal in
  let var_list = get_var_outside_of_hole context generalization goal_with_hole in
  let variables = sketch_variable_tbl generalization var_list in
  { label; goal = generalization.goal; goal_with_hole; hole; hole_type = typ_econstr; variables; } :: sketches

let get_possible_holes (context : LFContext.t) (g : Generalization.t) =
  let temp_terms = LFContext.get_terms context.env context.sigma [g.goal] in
  let terms_list = Hashtbl.fold (fun _ y acc -> y :: acc) temp_terms [] in
  let synth_terms = 
    List.filter
    (
      fun (term,typ) -> 
        (Constr.isApp (EConstr.to_constr context.sigma term) || Constr.isConstruct (EConstr.to_constr context.sigma term)) 
        && (not (Constr.is_Type (EConstr.to_constr context.sigma typ)))
        && (not (Constr.is_Prop (EConstr.to_constr context.sigma typ)))
    )
    terms_list in
  let result_tbl = Hashtbl.create (List.length synth_terms) in
  List.iteri 
  (fun i (term,typ) -> Hashtbl.add result_tbl (LFContext.e_str context term) (term,typ,i))
  synth_terms; result_tbl

let create_from_generalization (context : LFContext.t) (generalization : Generalization.t) =
  let synth_terms = get_possible_holes context generalization in
  let sketches = Hashtbl.fold (create_sketch context generalization) synth_terms [] in
  let subterm_sketches = Hashtbl.fold (create_subterm_sketch context generalization) synth_terms [] in
  sketches @ subterm_sketches

let generate (context : LFContext.t) (generalizations : Generalization.t list) : t list = 
  let sketches = List.map (create_from_generalization context) generalizations in 
  (List.flatten sketches)