(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*         Mehdi Dogguy, PPS laboratory, University Paris Diderot         *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*   Copyright 2010 Mehdi Dogguy                                          *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Dump info on .cmi, .cmo, .cmx, .cma, .cmxa, .cmxs files
   and on bytecode executables. *)

open Printf
open Misc
open Cmo_format

(* Command line options to prevent printing approximation,
   function code and CRC
 *)
let no_approx = ref false
let no_code = ref false
let no_crc = ref false
let no_debug = ref false
let do_test = ref false
let the_filename = ref ""

module Magic_number = Misc.Magic_number

module B = Ocaml_bytecomp
module C = Ocaml_common
module O = Ocaml_optcomp
module Compilation_unit = O.Compilation_unit
module Cf = Ocaml_common.Config
module I = B.Instruct
module Env = C.Env
module Envx = C.Envaux
module Id = C.Ident
open Format

let print_locations = ref true
let print_reloc_info = ref false

let relocate_event orig ev =
  ev.I.ev_pos <- orig + ev.I.ev_pos;
   match ev.ev_repr with 
   Event_parent repr -> repr := ev.ev_pos 
   | _ -> ()

let kind_string ev =
    (match ev.I.ev_kind with
      Event_before   -> "before"
    | Event_after _  -> "after"
    | Event_pseudo   -> "pseudo")

let info_string ev =
  (match ev.I.ev_info with
      Event_function -> "/fun"
    | Event_return _ -> "/ret"
    | Event_other    -> "")

let repr_string ev =
  (match ev.I.ev_repr with
    Event_none        -> ""
  | Event_parent _    -> "(repr)"
  | Event_child repr  -> Int.to_string !repr)

let get_env ev = 
  Envx.env_from_summary ev.I.ev_typenv

let print_summary_id ppf title id = 
  fprintf ppf " %s: " title;
  Id.print_with_scope ppf id;
  fprintf ppf  ";@ "

let print_summary_string ppf title s =
  fprintf ppf " %s: %s@ " title s

let next_summary summary =
      match summary with
      | Env.Env_empty -> None
      | Env_value (s, id, vd) -> Some s
      | Env_type (s, id, td) -> Some s
      | Env_extension (s, id, ec) -> Some s
      | Env_module (s, id, mp, md) -> Some s
      | Env_modtype (s, id, md) -> Some s
      | Env_class (s, id, cd) -> Some s
      | Env_cltype (s, id, ctd) -> Some s
      | Env_open (s, p) -> Some s
      | Env_functor_arg (s, id) -> Some s
      | Env_constraints (s, cstrs) -> Some s
      | Env_copy_types s -> Some s
      | Env_persistent (s, id) -> Some s
      | Env_value_unbound (s, n, r) -> Some s
      | Env_module_unbound (s, n, r) -> Some s

let print_value_desc ppf (vd: Types.value_description) =
  fprintf ppf "@[{";
  fprintf ppf "val_type=@ ";
  Print_typ.raw_type_expr ppf vd.val_type;
  ignore vd.val_kind;
  ignore vd.val_loc;
  ignore vd.val_attributes;
  ignore vd.val_uid;
  fprintf ppf "}@]"

      (*
    let ls = ev.ev_loc.loc_start in
    let le = ev.ev_loc.loc_end in
    fprintf ppf "ev_loc={File \"%s\", line %d, characters %d-%d},@ " ls.Lexing.pos_fname
      ls.Lexing.pos_lnum (ls.Lexing.pos_cnum - ls.Lexing.pos_bol)
      (le.Lexing.pos_cnum - ls.Lexing.pos_bol);
      *)

let myprint_loc ppf (loc: Location.t)  =
  if !print_locations then begin
    let ls = loc.loc_start in
    let filename = ls.pos_fname in
    if filename <> "_none_" then begin
      fprintf ppf ",@ ";
      Location.print_loc ppf loc;
    end else ()
  end else ()

let print_summary_item ppf summary =
  fprintf ppf "\n    ";
  match summary with
  | Env.Env_empty ->
      print_summary_string ppf "Env_empty" ""
  | Env_value (s, id, vd) ->
      fprintf ppf "@[<hov 2>";
      (* print_summary_id ppf "Env_value" id; *)
      Print_typ.value_description id ppf vd;
      myprint_loc ppf vd.val_loc;
      fprintf ppf ",@ ";
      (*
      Location.print_loc ppf vd.val_loc;
      fprintf ppf ",@ ";
      *)
      fprintf ppf "#atts=%d@ " (List.length vd.val_attributes);
      fprintf ppf "@]@;"
      (* print_value_desc ppf vd; *)
  | Env_type (s, id, td) ->
      fprintf ppf "@[<hov 2>";
      (* print_summary_id ppf "Env_type" id; *)
      Print_typ.type_declaration id ppf td;
      myprint_loc ppf td.type_loc;
      fprintf ppf "@]@;"
  | Env_extension (s, id, ec) ->
      fprintf ppf "@[<hov 2>";
      (* print_summary_id ppf "Env_extension" id; *)
      Print_typ.extension_constructor id ppf ec;
      myprint_loc ppf ec.ext_loc;
      fprintf ppf "@]@;"
  | Env_module (s, id, mp, md) ->
      print_summary_id ppf "Env_module" id;
  | Env_modtype (s, id, md) ->
      print_summary_id ppf "Env_modtype" id;
      Print_typ.modtype_declaration id ppf md
  | Env_class (s, id, cd) ->
      print_summary_id ppf "Env_class" id
  | Env_cltype (s, id, ctd) ->
      print_summary_id ppf "Env_cltype" id
  | Env_open (s, p) ->
      print_summary_string ppf "Env_open" (Path.name p)
  | Env_functor_arg (s, id) ->
      print_summary_id ppf "Env_functor_arg" id
  | Env_constraints (s, cstrs) ->
      print_summary_string ppf "Env_constraints" "cstrs"
  | Env_copy_types s ->
      print_summary_string ppf "Env_copy_types" ""
  | Env_persistent (s, id) ->
      print_summary_id ppf "Env_persistent" id
  | Env.Env_value_unbound (s, n, r) ->
      print_summary_string ppf "Env_value_unbound" 
      (String.concat " " [n; "reason"])
  | Env_module_unbound (s, n, r) ->
      print_summary_string ppf "Env_module_unbound" 
      (String.concat " " [n; "reason"])

let rec print_summary ppf summary =
  print_summary_item ppf summary;
  match next_summary summary with
  | None -> ()
  | Some s -> print_summary ppf s

let print_ident_tbl ppf  (title: string) (tbl: int Ident.tbl) =
  if tbl = Ident.empty then begin
    fprintf ppf "%s = empty@ " title
  end else begin
    fprintf ppf "@[<hv 2>%s {@ " title;
    Ident.iter (fun id idval -> 
      fprintf ppf "%s=%d@ " (Ident.name id) idval
      ) tbl;
    fprintf ppf "}@ @]";
  end
  
(* 
type compilation_env =
  { ce_stack: int Ident.tbl; (* Positions of variables in the stack *)
    ce_heap: int Ident.tbl;  (* Structure of the heap-allocated env *)
    ce_rec: int Ident.tbl }  (* Functions bound by the same let rec *)
   
*)
let print_comp_env ppf (ce : I.compilation_env) =
  let stack : int Ident.tbl = ce.ce_stack in
  let heap : int Ident.tbl = ce.ce_heap in
  let recs : int Ident.tbl = ce.ce_rec in
  if stack = Ident.empty && 
     heap = Ident.empty &&
     recs = Ident.empty 
  then () 
  else begin 
    fprintf ppf "@[<hv 2>ev_compenv{@;";
    print_ident_tbl ppf "ce_stack" stack;
    print_ident_tbl ppf "ce_heap" heap;
    print_ident_tbl ppf "ce_rec" recs;
    fprintf ppf "}@ @]";
  end

  (* From typing/subst.ml 
    type type_replacement =
      | Path of Path.t
      | Type_function of { params : type_expr list; body : type_expr }

    type t =
      { types: type_replacement Path.Map.t;
        modules: Path.t Path.Map.t;
        modtypes: module_type Path.Map.t;
        for_saving: bool;
        loc: Location.t option;
      }
  *)
  let print_subst ppf title (ts: Subst.t) =
    if ts = Subst.identity then begin
      (* fprintf ppf "%s is empty substitution,@ " title *)
      ()
    end else begin
      (* Unfortunately, the substitution is not made available *)
      fprintf ppf "{%s is non-empty (but opaque) substitution},@ " title
    end


(* From instruct.mli 

type debug_event =
  { mutable ev_pos: int;                (* Position in bytecode *)
    ev_module: string;                  (* Name of defining module *)
    ev_loc: Location.t;                 (* Location in source file *)
    ev_kind: debug_event_kind;          (* Before/after event *)
    ev_defname: string;                 (* Enclosing definition *)
    ev_info: debug_event_info;          (* Extra information *)
    ev_typenv: Env.summary;             (* Typing environment *)
    ev_typsubst: Subst.t;               (* Substitution over types *)
    ev_compenv: compilation_env;        (* Compilation environment *)
    ev_stacksize: int;                  (* Size of stack frame *)
    ev_repr: debug_event_repr }         (* Position of the representative *)

*)
let print_ev ppf (ev: I.debug_event)  j =
  fprintf ppf "@[<2>ev[%d]:{@ " j;
  fprintf ppf "pc=%d,@ " ev.I.ev_pos;
  fprintf ppf "ev_module=%s" ev.I.ev_module;
  myprint_loc ppf ev.ev_loc;
  fprintf ppf ",@ ev_kind=%s,@ " (kind_string ev);
  fprintf ppf "ev_defname=%s,@ " ev.ev_defname;
  fprintf ppf "ev_info=%s,@ " (info_string ev);
  fprintf ppf "ev_typenv={@;@[";
  print_summary ppf ev.ev_typenv;
  fprintf ppf "}@;@]@.";
  print_comp_env ppf ev.ev_compenv;
  print_subst ppf "ev_typsubst" ev.ev_typsubst;
  fprintf ppf "ev_stacksize=%d,@ " ev.ev_stacksize;
  fprintf ppf "ev_repr=%s,@ " (repr_string ev);
  fprintf ppf "}@]@.";
  ()

let dump_eventlist ppf orig ic =
  if !no_debug then () else begin
    fprintf ppf "@[{orig=%d,@ " orig;
    let in_pos = pos_in ic in
    printf "in_pos=%u,@ " in_pos;
    let evl : (I.debug_event list) = input_value ic in
    fprintf ppf "length evl=%d@." (List.length evl);
    let j = ref 0 in
    List.iter (fun ev ->
      relocate_event orig ev;
      print_ev  ppf ev !j;
      j := !j + 1;
      ) evl;
    let (dirs : string list) = input_value ic in
    fprintf ppf "@[<v 2>dirs=";
    List.iter (fun dir -> fprintf ppf "%s@ " dir) dirs;
    fprintf ppf "}@]@.";
  end

let dump_eventlists ppf ic =
  if !no_debug then () else begin
    let debug_len = C.Bytesections.seek_section ic "DBUG" in
    fprintf ppf "{debug_len=%d\n" debug_len;
    let pos = pos_in ic in
    fprintf ppf "pos=%d\n" pos;

    let num_eventlists = input_binary_int ic in
    fprintf ppf "num_eventlists=%d\n" num_eventlists;
    for i = 1 to num_eventlists do
      let orig = input_binary_int ic in
      dump_eventlist ppf orig ic
    done;
    fprintf ppf "}\n";
  end

let input_stringlist ic len =
  let get_string_list sect len =
    let rec fold s e acc =
      if e != len then
        if sect.[e] = '\000' then
          fold (e+1) (e+1) (String.sub sect s (e-s) :: acc)
        else fold s (e+1) acc
      else acc
    in fold 0 0 []
  in
  let sect = really_input_string ic len in
  get_string_list sect len

let dummy_crc = String.make 32 '-'
let null_crc = String.make 32 '0'

let string_of_crc crc = if !no_crc then null_crc else Digest.to_hex crc

let print_name_crc (name, crco) =
  let crc =
    match crco with
      None -> dummy_crc
    | Some crc -> string_of_crc crc
  in
    printf "\t%s\t%s\n" crc name

let print_line name =
  printf "\t%s\n" name

let print_required_global id =
  printf "\t%s\n" (Ident.name id)

let print_cmo_infos ic cu =
  printf "Unit name: %s\n" cu.cu_name;
  print_string "Interfaces imported:\n";
  List.iter print_name_crc cu.cu_imports;
  print_string "Required globals:\n";
  List.iter print_required_global cu.cu_required_globals;
  printf "Uses unsafe features: ";
  (match cu.cu_primitives with
    | [] -> printf "no\n"
    | l  ->
        printf "YES\n";
        printf "Primitives declared in this module:\n";
        List.iter print_line l);
  printf "Force link: %s\n" (if cu.cu_force_link then "YES" else "no");
  let debug_size = cu.cu_debugsize in
  printf "debug_size=%u\n" debug_size;
  if debug_size > 0 then begin
    printf "cu_debug=%u@." cu.cu_debug;
    let in_pos = pos_in ic in
    printf "in_pos=%u@." in_pos;
    
    seek_in ic cu.cu_debug;
    dump_eventlist std_formatter 0 ic;
    
  end

let print_spaced_string s =
  printf " %s" s

let print_cma_infos ic (lib : Cmo_format.library) =
  printf "Force custom: %s\n" (if lib.lib_custom then "YES" else "no");
  printf "Extra C object files:";
  (* PR#4949: print in linking order *)
  List.iter print_spaced_string (List.rev lib.lib_ccobjs);
  printf "\nExtra C options:";
  List.iter print_spaced_string (List.rev lib.lib_ccopts);
  printf "\n";
  print_string "Extra dynamically-loaded libraries:";
  List.iter print_spaced_string (List.rev lib.lib_dllibs);
  printf "\n";
  List.iter (print_cmo_infos ic) lib.lib_units

let print_cmi_infos name crcs =
  printf "Unit name: %s\n" name;
  printf "Interfaces imported:\n";
  List.iter print_name_crc crcs

let print_cmt_infos cmt =
  let open Cmt_format in
  printf "Cmt unit name: %s\n" cmt.cmt_modname;
  print_string "Cmt interfaces imported:\n";
  List.iter print_name_crc cmt.cmt_imports;
  printf "Source file: %s\n"
         (match cmt.cmt_sourcefile with None -> "(none)" | Some f -> f);
  printf "Compilation flags:";
  Array.iter print_spaced_string cmt.cmt_args;
  printf "\nLoad path:";
  List.iter print_spaced_string cmt.cmt_loadpath;
  printf "\n";
  printf "cmt interface digest: %s\n"
    (match cmt.cmt_interface_digest with
     | None -> ""
     | Some crc -> string_of_crc crc)

let print_general_infos name crc defines cmi cmx =
  printf "Name: %s\n" name;
  printf "CRC of implementation: %s\n" (string_of_crc crc);
  printf "Globals defined:\n";
  List.iter print_line defines;
  printf "Interfaces imported:\n";
  List.iter print_name_crc cmi;
  printf "Implementations imported:\n";
  List.iter print_name_crc cmx

let print_global_table table =
  printf "Globals defined:\n";
  Symtable.iter_global_map
    (fun id _ -> print_line (Ident.name id))
    table

open Cmx_format
open Cmxs_format

let print_cmx_infos (ui, crc) =
  print_general_infos
    ui.ui_name crc ui.ui_defines ui.ui_imports_cmi ui.ui_imports_cmx;
  begin match ui.ui_export_info with
  | Clambda approx ->
    if not !no_approx then begin
      printf "Clambda approximation:\n";
      Format.fprintf Format.std_formatter "  %a@." Printclambda.approx approx
    end else
      Format.printf "Clambda unit@.";
  | Flambda export ->
    if not !no_approx || not !no_code then
      printf "Flambda export information:\n"
    else
      printf "Flambda unit\n";
    if not !no_approx then begin
      let cu =
        Compilation_unit.create (Ident.create_persistent ui.ui_name)
          (Linkage_name.create "__dummy__")
      in
      Compilation_unit.set_current cu;
      let root_symbols =
        List.map (fun s ->
            Symbol.of_global_linkage cu (Linkage_name.create ("caml"^s)))
          ui.ui_defines
      in
      Format.printf "approximations@ %a@.@."
        Export_info.print_approx (export, root_symbols)
    end;
    if not !no_code then
      Format.printf "functions@ %a@.@."
        Export_info.print_functions export
  end;
  let pr_funs _ fns =
    List.iter (fun arity -> printf " %d" arity) fns in
  printf "Currying functions:%a\n" pr_funs ui.ui_curry_fun;
  printf "Apply functions:%a\n" pr_funs ui.ui_apply_fun;
  printf "Send functions:%a\n" pr_funs ui.ui_send_fun;
  printf "Force link: %s\n" (if ui.ui_force_link then "YES" else "no")

let print_cmxa_infos (lib : Cmx_format.library_infos) =
  printf "Extra C object files:";
  List.iter print_spaced_string (List.rev lib.lib_ccobjs);
  printf "\nExtra C options:";
  List.iter print_spaced_string (List.rev lib.lib_ccopts);
  printf "\n";
  List.iter print_cmx_infos lib.lib_units

let print_cmxs_infos header =
  List.iter
    (fun ui ->
       print_general_infos
         ui.dynu_name
         ui.dynu_crc
         ui.dynu_defines
         ui.dynu_imports_cmi
         ui.dynu_imports_cmx)
    header.dynu_units

let p_title title = printf "%s:\n" title

let p_section title = function
  | [] -> ()
  | l ->
      p_title title;
      List.iter print_name_crc l

let p_list title print = function
  | [] -> ()
  | l ->
      p_title title;
      List.iter print l

let dump_byte ic =
  Bytesections.read_toc ic;
  let toc = Bytesections.toc () in
  let toc = List.sort Stdlib.compare toc in
  List.iter
    (fun (section, _) ->
       try
         let len = Bytesections.seek_section ic section in
         if len > 0 then match section with
           | "CRCS" ->
               p_section
                 "Imported units"
                 (input_value ic : (string * Digest.t option) list)
           | "DLLS" ->
               p_list
                 "Used DLLs"
                 print_line
                 (input_stringlist ic len)
           | "DLPT" ->
               p_list
                 "Additional DLL paths"
                 print_line
                 (input_stringlist ic len)
           | "PRIM" ->
               p_list
                 "Primitives used"
                 print_line
                 (input_stringlist ic len)
           | "SYMB" ->
               print_global_table (input_value ic)
           | "DBUG" ->
               dump_eventlists std_formatter ic
           | _ -> ()
       with _ -> ()
    )
    toc

let find_dyn_offset filename =
  match Binutils.read filename with
  | Ok t ->
      Binutils.symbol_offset t "caml_plugin_header"
  | Error _ ->
      None

let exit_err msg = print_endline msg; exit 2
let exit_errf fmt = Printf.ksprintf exit_err fmt

let exit_magic_msg msg =
  exit_errf
     "Wrong magic number:\n\
      this tool only supports object files produced by compiler version\n\
      \t%s\n\
      %s"
    Sys.ocaml_version msg

let exit_magic_error ~expected_kind err =
  exit_magic_msg Magic_number.(match err with
    | Parse_error err -> explain_parse_error expected_kind err
    | Unexpected_error err -> explain_unexpected_error err)

(* assume that 'ic' is already positioned at the right place
   depending on the format (usually right after the magic number,
   but Exec and Cmxs differ) *)
let dump_obj_by_kind filename ic obj_kind =
  let open Magic_number in
  match obj_kind with
    | Cmo ->
       let cu_pos = input_binary_int ic in
       seek_in ic cu_pos;
       let cu = (input_value ic : compilation_unit) in
       print_cmo_infos ic cu;
       close_in ic;
    | Cma ->
       let toc_pos = input_binary_int ic in
       seek_in ic toc_pos;
       let toc = (input_value ic : library) in
       print_cma_infos ic toc;
       close_in ic
    | Cmi | Cmt ->
       close_in ic;
       let cmi, cmt = Cmt_format.read filename in
       begin match cmi with
         | None -> ()
         | Some cmi ->
            print_cmi_infos cmi.Cmi_format.cmi_name cmi.Cmi_format.cmi_crcs
       end;
       begin match cmt with
         | None -> ()
         | Some cmt -> print_cmt_infos cmt
       end
    | Cmx _config ->
       let ui = (input_value ic : unit_infos) in
       let crc = Digest.input ic in
       close_in ic;
       print_cmx_infos (ui, crc)
    | Cmxa _config ->
       let li = (input_value ic : library_infos) in
       close_in ic;
       print_cmxa_infos li
    | Exec ->
       (* no assumptions on [ic] position,
          [dump_byte] will seek at the right place *)
       dump_byte ic;
       close_in ic
    | Cmxs ->
       (* we assume we are at the offset of the dynamic information,
          as returned by [find_dyn_offset]. *)
       let header = (input_value ic : dynheader) in
       close_in ic;
       print_cmxs_infos header;
    | Ast_impl | Ast_intf ->
       exit_errf "The object file type %S \
                  is currently unsupported by this tool."
         (human_name_of_kind obj_kind)

let dump_obj filename =
  the_filename := filename;
  if !do_test then begin
    printf "File %s\n" filename;
    let ic = open_in_bin filename in
    seek_in ic 28;
    dump_eventlist std_formatter 0 ic;
    ()
  end else
  let open Magic_number in
  let dump_standard ic =
    match read_current_info ~expected_kind:None ic with
      | Error ((Unexpected_error _) as err) ->
         exit_magic_error ~expected_kind:None err
      | Ok { kind; version = _ } ->
         dump_obj_by_kind filename ic kind;
         Ok ()
      | Error (Parse_error head_error) ->
         Error head_error
  and dump_exec ic =
    let pos_trailer = in_channel_length ic - Magic_number.magic_length in
    let _ = seek_in ic pos_trailer in
    let expected_kind = Some Exec in
    match read_current_info ~expected_kind ic with
      | Error ((Unexpected_error _) as err) ->
         exit_magic_error ~expected_kind err
      | Ok _ ->
         dump_obj_by_kind filename ic Exec;
         Ok ()
      | Error (Parse_error _)  ->
         Error ()
  and dump_cmxs ic =
    flush stdout;
    match find_dyn_offset filename with
      | None ->
         exit_errf "Unable to read info on %s %s."
           (human_name_of_kind Cmxs) filename
      | Some offset ->
         LargeFile.seek_in ic offset;
         let header = (input_value ic : dynheader) in
         let expected_kind = Some Cmxs in
         match parse header.dynu_magic with
           | Error err ->
              exit_magic_error ~expected_kind (Parse_error err)
           | Ok info ->
         match check_current Cmxs info with
           | Error err ->
              exit_magic_error ~expected_kind (Unexpected_error err)
           | Ok () ->
         LargeFile.seek_in ic offset;
         dump_obj_by_kind filename ic Cmxs;
         ()
  in
  printf "@[<v>File %s@ " filename;
  let ic = open_in_bin filename in
  match dump_standard ic with
    | Ok () -> printf "@]"
    | Error head_error ->
  match dump_exec ic with
    | Ok () -> printf "@]"
    | Error () ->
  if Filename.check_suffix filename ".cmxs"
  then (dump_cmxs ic; printf "@]")
  else (printf "@]";exit_magic_error ~expected_kind:None (Parse_error head_error))

let arg_list = [
  "-no-approx", Arg.Set no_approx,
    " Do not print module approximation information";
  "-no-code", Arg.Set no_code,
    " Do not print code from exported flambda functions";
  "-no-debug", Arg.Set no_debug,
    " Do not print debug information";
  "-test", Arg.Set do_test,
    " Do special test";
  "-null-crc", Arg.Set no_crc, " Print a null CRC for imported interfaces";
  "-args", Arg.Expand Arg.read_arg,
     "<file> Read additional newline separated command line arguments \n\
     \      from <file>";
  "-args0", Arg.Expand Arg.read_arg0,
     "<file> Read additional NUL separated command line arguments from \n\
     \      <file>";
]
let arg_usage =
   Printf.sprintf "%s [OPTIONS] FILES : give information on files" Sys.argv.(0)

let main() =
  Arg.parse_expand arg_list dump_obj arg_usage;
  exit 0

let _ = main ()