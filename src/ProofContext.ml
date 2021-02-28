type proof_context = 
  {
    hypotheses : string list;
    goal : string;
    functions : string list;
    vars : string list;
    samples :  string list list;
    fname: string;
    dir: string;
    full_context: string;
  }

type coq_context = 
  {
    env : Environ.env;
    sigma : Evd.evar_map;
  }

let hyp_to_string hyp = 
  List.fold_left (fun acc h ->  acc ^ "\n" ^ h) "" hyp

let to_string p_ctxt = 
  let hyp_str = hyp_to_string p_ctxt.hypotheses
  in hyp_str ^ "\n" ^ "=========================" ^ p_ctxt.goal
  
let get_fname full_context =
  let library = List.hd (String.split_on_char '\n' full_context)
  in List.hd (List.rev (String.split_on_char '.' library))
  

