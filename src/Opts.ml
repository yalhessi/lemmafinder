open Goptions

let enable_quickchick = ref true

let _ =
  let gdopt=
    { optdepr=false;
      optkey=["Lfind";"QuickChick"];
      (* optname="Use QuickChick"; *)
      optread=(fun () -> !enable_quickchick);
      optwrite=(fun b -> enable_quickchick := b)}
  in
  declare_bool_option gdopt

let enable_proverbot = ref true

let _ =
  let gdopt=
    { optdepr=false;
      optkey=["Lfind";"Proverbot"];
      (* optname="Use Proverbot"; *)
      optread=(fun () -> !enable_proverbot);
      optwrite=(fun b -> enable_proverbot := b)}
  in
  declare_bool_option gdopt
  
  