type proof_context = 
  {
    hypotheses : string list;
    goal : string;
    functions : string list;
    samples :  string list list
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
  
