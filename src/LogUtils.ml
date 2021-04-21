let write_tbl_to_log tbl tbl_name=
  Log.debug ("Contents of " ^ tbl_name);
  Hashtbl.iter (fun k v -> Log.debug (Consts.fmt "%s -> %s" k v)) tbl; ()

let write_list_to_log lst name = 
  Log.debug ("Contents of " ^ name);
  List.iter (fun l -> Log.debug l) lst; ()