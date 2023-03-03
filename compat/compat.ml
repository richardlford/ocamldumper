[%%if ocaml_version < (4,13,0)]
  let starts_with ~prefix s =
    let re = Str.regexp_string prefix in
    try
      ignore (Str.search_forward re s 0);
      true
    with Not_found -> false
[%%else]
  let starts_with ~prefix s =
    String.starts_with ~prefix s
[%%endif]

[%%if ocaml_version < (4,13,0)]
  let realpath fname =
    if Filename.is_relative fname then
      Sys.getcwd() ^ "/" ^ fname
    else
      fname

[%%else]
let realpath = Unix.realpath
[%%endif]

[%%if ocaml_version < (5,0,0)]
let load_path_init = Load_path.init
[%%else]
let load_path_init path = 
  Load_path.reset();
  List.iter Load_path.add_dir (List.rev path)
  
[%%endif]


(* Save the following as a template*)
[%%if ocaml_version < (4,13,0)]
[%%else]
[%%endif]
