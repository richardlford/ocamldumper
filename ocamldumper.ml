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
   and on bytecode executables. 

   This file is an enhanced version of a combination of the OCaml
   dumpobj and objinfo utilities.
*)

open Printf
open Misc
open Cmo_format


(* Command line options *)
let the_filename = ref ""
let print_approx_flag = ref true
let print_code_flag = ref true
let print_crc_flag = ref true
let print_debug_flag = ref true
let print_dirs_flag = ref true
let print_dlls_flag = ref true
let print_dll_paths_flag = ref true
let print_full_events_flag = ref false
let print_globals_flag = ref true
let print_imports_flag = ref true
let print_locations_flag = ref true
let print_primitives_flag = ref true
let print_reloc_info_flag = ref true
let print_source_flag = ref true

module Magic_number = Misc.Magic_number

open Lambda
open Format
open Opcodes
open Opnames

let () =
  Load_path.init []

(* Read signed and unsigned integers *)

let inputu ic =
  let b1 = input_byte ic in
  let b2 = input_byte ic in
  let b3 = input_byte ic in
  let b4 = input_byte ic in
  (b4 lsl 24) + (b3 lsl 16) + (b2 lsl 8) + b1

let inputs ic =
  let b1 = input_byte ic in
  let b2 = input_byte ic in
  let b3 = input_byte ic in
  let b4 = input_byte ic in
  let b4' = if b4 >= 128 then b4-256 else b4 in
  (b4' lsl 24) + (b3 lsl 16) + (b2 lsl 8) + b1

type global_table_entry =
    Empty
  | Global of Ident.t
  | Constant of Obj.t

let start = ref 0                              (* Position of beg. of code *)
let reloc = ref ([] : (reloc_info * int) list) (* Relocation table *)
let globals = ref ([||] : global_table_entry array) (* Global map *)
let primitives = ref ([||] : string array)     (* Table of primitives *)
let objfile = ref true                        (* true if dumping a .cmo *)

(* Events (indexed by PC) *)
let event_table = (Hashtbl.create 253 : (int, Instruct.debug_event) Hashtbl.t)

let relocate_event orig ev =
  ev.Instruct.ev_pos <- orig + ev.Instruct.ev_pos;
   match ev.ev_repr with 
   Event_parent repr -> repr := ev.ev_pos 
   | _ -> ()

let record_events orig evl =
  List.iter
    (fun ev ->
      relocate_event orig ev;
      Hashtbl.add event_table ev.ev_pos ev)
    evl

(* Print a structured constant *)

let print_float f =
  if String.contains f '.'
  then printf "%s" f
  else printf "%s." f
;;

let rec print_struct_const = function
    Const_base(Const_int i) -> printf "%d" i
  | Const_base(Const_float f) -> print_float f
  | Const_base(Const_string (s, _, _)) -> printf "%S" s
  | Const_immstring s -> printf "%S" s
  | Const_base(Const_char c) -> printf "%C" c
  | Const_base(Const_int32 i) -> printf "%ldl" i
  | Const_base(Const_nativeint i) -> printf "%ndn" i
  | Const_base(Const_int64 i) -> printf "%LdL" i
  | Const_block(tag, args) ->
      printf "<%d>" tag;
      begin match args with
        [] -> ()
      | [a1] ->
          printf "("; print_struct_const a1; printf ")"
      | a1::al ->
          printf "("; print_struct_const a1;
          List.iter (fun a -> printf ", "; print_struct_const a) al;
          printf ")"
      end
  | Const_float_array a ->
      printf "[|";
      List.iter (fun f -> print_float f; printf "; ") a;
      printf "|]"

(* Print an obj *)

let same_custom x y =
  Obj.field x 0 = Obj.field (Obj.repr y) 0

let rec print_obj x =
  if Obj.is_block x then begin
    let tag = Obj.tag x in
    if tag = Obj.string_tag then
        printf "%S" (Obj.magic x : string)
    else if tag = Obj.double_tag then
        printf "%.12g" (Obj.magic x : float)
    else if tag = Obj.double_array_tag then begin
        let a = (Obj.magic x : floatarray) in
        printf "[|";
        for i = 0 to Array.Floatarray.length a - 1 do
          if i > 0 then printf ", ";
          printf "%.12g" (Array.Floatarray.get a i)
        done;
        printf "|]"
    end else if tag = Obj.custom_tag && same_custom x 0l then
        printf "%ldl" (Obj.magic x : int32)
    else if tag = Obj.custom_tag && same_custom x 0n then
        printf "%ndn" (Obj.magic x : nativeint)
    else if tag = Obj.custom_tag && same_custom x 0L then
        printf "%LdL" (Obj.magic x : int64)
    else if tag < Obj.no_scan_tag then begin
        printf "<%d>" (Obj.tag x);
        match Obj.size x with
          0 -> ()
        | 1 ->
            printf "("; print_obj (Obj.field x 0); printf ")"
        | n ->
            printf "("; print_obj (Obj.field x 0);
            for i = 1 to n - 1 do
              printf ", "; print_obj (Obj.field x i)
            done;
            printf ")"
    end else
        printf "<tag %d>" tag
  end else
    printf "%d" (Obj.magic x : int)

(* Current position in input file *)

let currpos ic =
  pos_in ic - !start

(* Access in the relocation table *)

let rec rassoc key = function
    [] -> raise Not_found
  | (a,b) :: l -> if b = key then a else rassoc key l

let find_reloc ic =
  rassoc (pos_in ic - !start) !reloc

(* Symbolic printing of global names, etc *)

let print_global item =
  match item with
    Global id -> print_string(Ident.name id)
  | Constant obj -> print_obj obj
  | _ -> print_string "???"

let print_getglobal_name ic =
  if !objfile then begin
    begin try
      match find_reloc ic with
          Reloc_getglobal id -> print_string (Ident.name id)
        | Reloc_literal sc -> print_struct_const sc
        | _ -> print_string "<wrong reloc>"
    with Not_found ->
      print_string "<no reloc>"
    end;
    ignore (inputu ic);
  end
  else begin
    let n = inputu ic in
    if n >= Array.length !globals || n < 0
    then print_string "<global table overflow>"
    else print_global !globals.(n) 
  end

let print_setglobal_name ic =
  if !objfile then begin
    begin try
      match find_reloc ic with
        Reloc_setglobal id -> print_string (Ident.name id)
      | _ -> print_string "<wrong reloc>"
    with Not_found ->
      print_string "<no reloc>"
    end;
    ignore (inputu ic);
  end
  else begin
    let n = inputu ic in
    if n >= Array.length !globals || n < 0
    then print_string "<global table overflow>"
    else match !globals.(n) with
           Global id -> print_string(Ident.name id)
         | _ -> print_string "???"
  end

let print_primitive ic =
  if !objfile then begin
    begin try
      match find_reloc ic with
        Reloc_primitive s -> print_string s
      | _ -> print_string "<wrong reloc>"
    with Not_found ->
      print_string "<no reloc>"
    end;
    ignore (inputu ic);
  end
  else begin
    let n = inputu ic in
    if n >= Array.length !primitives || n < 0
    then print_int n
    else print_string !primitives.(n)
  end

  (* Disassemble one instruction *)

let currpc ic =
  currpos ic / 4

type shape =
  | Nothing
  | Uint
  | Sint
  | Uint_Uint
  | Disp
  | Uint_Disp
  | Sint_Disp
  | Getglobal
  | Getglobal_Uint
  | Setglobal
  | Primitive
  | Uint_Primitive
  | Switch
  | Closurerec
  | Pubmet
;;


let op_shapes = [
  opACC0, Nothing;
  opACC1, Nothing;
  opACC2, Nothing;
  opACC3, Nothing;
  opACC4, Nothing;
  opACC5, Nothing;
  opACC6, Nothing;
  opACC7, Nothing;
  opACC, Uint;
  opPUSH, Nothing;
  opPUSHACC0, Nothing;
  opPUSHACC1, Nothing;
  opPUSHACC2, Nothing;
  opPUSHACC3, Nothing;
  opPUSHACC4, Nothing;
  opPUSHACC5, Nothing;
  opPUSHACC6, Nothing;
  opPUSHACC7, Nothing;
  opPUSHACC, Uint;
  opPOP, Uint;
  opASSIGN, Uint;
  opENVACC1, Nothing;
  opENVACC2, Nothing;
  opENVACC3, Nothing;
  opENVACC4, Nothing;
  opENVACC, Uint;
  opPUSHENVACC1, Nothing;
  opPUSHENVACC2, Nothing;
  opPUSHENVACC3, Nothing;
  opPUSHENVACC4, Nothing;
  opPUSHENVACC, Uint;
  opPUSH_RETADDR, Disp;
  opAPPLY, Uint;
  opAPPLY1, Nothing;
  opAPPLY2, Nothing;
  opAPPLY3, Nothing;
  opAPPTERM, Uint_Uint;
  opAPPTERM1, Uint;
  opAPPTERM2, Uint;
  opAPPTERM3, Uint;
  opRETURN, Uint;
  opRESTART, Nothing;
  opGRAB, Uint;
  opCLOSURE, Uint_Disp;
  opCLOSUREREC, Closurerec;
  opOFFSETCLOSUREM3, Nothing;
  opOFFSETCLOSURE0, Nothing;
  opOFFSETCLOSURE3, Nothing;
  opOFFSETCLOSURE, Sint;  (* was Uint *)
  opPUSHOFFSETCLOSUREM3, Nothing;
  opPUSHOFFSETCLOSURE0, Nothing;
  opPUSHOFFSETCLOSURE3, Nothing;
  opPUSHOFFSETCLOSURE, Sint; (* was Nothing *)
  opGETGLOBAL, Getglobal;
  opPUSHGETGLOBAL, Getglobal;
  opGETGLOBALFIELD, Getglobal_Uint;
  opPUSHGETGLOBALFIELD, Getglobal_Uint;
  opSETGLOBAL, Setglobal;
  opATOM0, Nothing;
  opATOM, Uint;
  opPUSHATOM0, Nothing;
  opPUSHATOM, Uint;
  opMAKEBLOCK, Uint_Uint;
  opMAKEBLOCK1, Uint;
  opMAKEBLOCK2, Uint;
  opMAKEBLOCK3, Uint;
  opMAKEFLOATBLOCK, Uint;
  opGETFIELD0, Nothing;
  opGETFIELD1, Nothing;
  opGETFIELD2, Nothing;
  opGETFIELD3, Nothing;
  opGETFIELD, Uint;
  opGETFLOATFIELD, Uint;
  opSETFIELD0, Nothing;
  opSETFIELD1, Nothing;
  opSETFIELD2, Nothing;
  opSETFIELD3, Nothing;
  opSETFIELD, Uint;
  opSETFLOATFIELD, Uint;
  opVECTLENGTH, Nothing;
  opGETVECTITEM, Nothing;
  opSETVECTITEM, Nothing;
  opGETSTRINGCHAR, Nothing;
  opGETBYTESCHAR, Nothing;
  opSETBYTESCHAR, Nothing;
  opBRANCH, Disp;
  opBRANCHIF, Disp;
  opBRANCHIFNOT, Disp;
  opSWITCH, Switch;
  opBOOLNOT, Nothing;
  opPUSHTRAP, Disp;
  opPOPTRAP, Nothing;
  opRAISE, Nothing;
  opCHECK_SIGNALS, Nothing;
  opC_CALL1, Primitive;
  opC_CALL2, Primitive;
  opC_CALL3, Primitive;
  opC_CALL4, Primitive;
  opC_CALL5, Primitive;
  opC_CALLN, Uint_Primitive;
  opCONST0, Nothing;
  opCONST1, Nothing;
  opCONST2, Nothing;
  opCONST3, Nothing;
  opCONSTINT, Sint;
  opPUSHCONST0, Nothing;
  opPUSHCONST1, Nothing;
  opPUSHCONST2, Nothing;
  opPUSHCONST3, Nothing;
  opPUSHCONSTINT, Sint;
  opNEGINT, Nothing;
  opADDINT, Nothing;
  opSUBINT, Nothing;
  opMULINT, Nothing;
  opDIVINT, Nothing;
  opMODINT, Nothing;
  opANDINT, Nothing;
  opORINT, Nothing;
  opXORINT, Nothing;
  opLSLINT, Nothing;
  opLSRINT, Nothing;
  opASRINT, Nothing;
  opEQ, Nothing;
  opNEQ, Nothing;
  opLTINT, Nothing;
  opLEINT, Nothing;
  opGTINT, Nothing;
  opGEINT, Nothing;
  opOFFSETINT, Sint;
  opOFFSETREF, Sint;
  opISINT, Nothing;
  opGETMETHOD, Nothing;
  opGETDYNMET, Nothing;
  opGETPUBMET, Pubmet;
  opBEQ, Sint_Disp;
  opBNEQ, Sint_Disp;
  opBLTINT, Sint_Disp;
  opBLEINT, Sint_Disp;
  opBGTINT, Sint_Disp;
  opBGEINT, Sint_Disp;
  opULTINT, Nothing;
  opUGEINT, Nothing;
  opBULTINT, Uint_Disp;
  opBUGEINT, Uint_Disp;
  opSTOP, Nothing;
  opEVENT, Nothing;
  opBREAK, Nothing;
  opRERAISE, Nothing;
  opRAISE_NOTRACE, Nothing;
];;

(* Dump relocation info *)

let print_reloc (info, pos) =
  printf "    %d    (%d)    " pos (pos/4);
  match info with
    Reloc_literal sc -> print_struct_const sc; printf "@."
  | Reloc_getglobal id -> printf "require    %s@." (Ident.name id)
  | Reloc_setglobal id -> printf "provide    %s@." (Ident.name id)
  | Reloc_primitive s -> printf "prim    %s@." s


let kind_string ev =
    (match ev.Instruct.ev_kind with
      Event_before   -> "before"
    | Event_after _  -> "after"
    | Event_pseudo   -> "pseudo")

let info_string ev =
  (match ev.Instruct.ev_info with
      Event_function -> "/fun"
    | Event_return _ -> "/ret"
    | Event_other    -> "")

let repr_string ev =
  (match ev.Instruct.ev_repr with
    Event_none        -> ""
  | Event_parent _    -> "(repr)"
  | Event_child repr  -> Int.to_string !repr)

let get_env ev = 
  Envaux.env_from_summary ev.Instruct.ev_typenv

let print_summary_id title id = 
  printf " %s: " title;
  Ident.print_with_scope std_formatter id;
  printf  ";@ "

let print_summary_string title s =
  printf " %s: %s@ " title s

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

let print_value_desc (vd: Types.value_description) =
  printf "@[{";
  printf "val_type=@ ";
  Xprinttyp.raw_type_expr std_formatter vd.val_type;
  ignore vd.val_kind;
  ignore vd.val_loc;
  ignore vd.val_attributes;
  ignore vd.val_uid;
  printf "}@]"

      (*
    let ls = ev.ev_loc.loc_start in
    let le = ev.ev_loc.loc_end in
    printf "ev_loc={File \"%s\", line %d, characters %d-%d},@ " ls.Lexing.pos_fname
      ls.Lexing.pos_lnum (ls.Lexing.pos_cnum - ls.Lexing.pos_bol)
      (le.Lexing.pos_cnum - ls.Lexing.pos_bol);
      *)

let myprint_loc (loc: Location.t)  =
  if !print_locations_flag then begin
    let ls = loc.loc_start in
    let filename = ls.pos_fname in
    if filename <> "_none_" then begin
      printf ",@ ";
      Location.print_loc std_formatter loc;
    end
  end

let print_summary_item summary =
  printf "@.    ";
  match summary with
  | Env.Env_empty ->
      print_summary_string "Env_empty" ""
  | Env_value (s, id, vd) ->
      printf "@[<hov 2>";
      (* print_summary_id "Env_value" id; *)
      Xprinttyp.value_description id std_formatter vd;
      myprint_loc vd.val_loc;
      printf ",@ ";
      (*
      Location.print_loc vd.val_loc;
      printf ",@ ";
      *)
      printf "#atts=%d@ " (List.length vd.val_attributes);
      printf "@]@;"
      (* print_value_desc vd; *)
  | Env_type (s, id, td) ->
      printf "@[<hov 2>";
      (* print_summary_id "Env_type" id; *)
      Xprinttyp.type_declaration id std_formatter td;
      myprint_loc td.type_loc;
      printf "@]@;"
  | Env_extension (s, id, ec) ->
      printf "@[<hov 2>";
      (* print_summary_id "Env_extension" id; *)
      Xprinttyp.extension_constructor id std_formatter ec;
      myprint_loc ec.ext_loc;
      printf "@]@;"
  | Env_module (s, id, mp, md) ->
      print_summary_id "Env_module" id;
  | Env_modtype (s, id, md) ->
      print_summary_id "Env_modtype" id;
      Xprinttyp.modtype_declaration id std_formatter md
  | Env_class (s, id, cd) ->
      print_summary_id "Env_class" id
  | Env_cltype (s, id, ctd) ->
      print_summary_id "Env_cltype" id
  | Env_open (s, p) ->
      print_summary_string "Env_open" (Path.name p)
  | Env_functor_arg (s, id) ->
      print_summary_id "Env_functor_arg" id
  | Env_constraints (s, cstrs) ->
      print_summary_string "Env_constraints" "cstrs"
  | Env_copy_types s ->
      print_summary_string "Env_copy_types" ""
  | Env_persistent (s, id) ->
      print_summary_id "Env_persistent" id
  | Env.Env_value_unbound (s, n, r) ->
      print_summary_string "Env_value_unbound" 
      (String.concat " " [n; "reason"])
  | Env_module_unbound (s, n, r) ->
      print_summary_string "Env_module_unbound" 
      (String.concat " " [n; "reason"])

let rec print_summary summary =
  print_summary_item summary;
  match next_summary summary with
  | None -> ()
  | Some s -> print_summary s

let print_ident_tbl  (title: string) (tbl: int Ident.tbl) =
  if tbl = Ident.empty then begin
    printf "%s = empty@ " title
  end else begin
    printf "@[<hv 2>%s {@ " title;
    Ident.iter (fun id idval -> 
      printf "%s=%d@ " (Ident.name id) idval
      ) tbl;
    printf "}@ @]";
  end
  
(* 
type compilation_env =
  { ce_stack: int Ident.tbl; (* Positions of variables in the stack *)
    ce_heap: int Ident.tbl;  (* Structure of the heap-allocated env *)
    ce_rec: int Ident.tbl }  (* Functions bound by the same let rec *)
   
*)
let print_comp_env (ce : Instruct.compilation_env) =
  let stack : int Ident.tbl = ce.ce_stack in
  let heap : int Ident.tbl = ce.ce_heap in
  let recs : int Ident.tbl = ce.ce_rec in
  if stack = Ident.empty && 
     heap = Ident.empty &&
     recs = Ident.empty 
  then () 
  else begin 
    printf "@[<hv 2>ev_compenv{@;";
    print_ident_tbl "ce_stack" stack;
    print_ident_tbl "ce_heap" heap;
    print_ident_tbl "ce_rec" recs;
    printf "}@ @]";
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
  let print_subst title (ts: Subst.t) =
    if ts = Subst.identity then begin
      (* printf "%s is empty substitution,@ " title *)
      ()
    end else begin
      (* Unfortunately, the substitution is not made available *)
      printf "{%s is non-empty (but opaque) substitution},@ " title
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

let print_ev (ev: Instruct.debug_event) =
  if !print_source_flag then
    Show_source.show_point ev true;
  printf "pc=%d,@ " ev.Instruct.ev_pos;
  printf "ev_module=%s" ev.Instruct.ev_module;
  myprint_loc ev.ev_loc;
  printf ",@ ev_kind=%s,@ " (kind_string ev);
  printf "ev_defname=%s,@ " ev.ev_defname;
  printf "ev_info=%s,@ " (info_string ev);
  printf "ev_typenv={@;@[";
  print_summary ev.ev_typenv;
  printf "}@;@]@.";
  print_comp_env ev.ev_compenv;
  print_subst "ev_typsubst" ev.ev_typsubst;
  printf "ev_stacksize=%d,@ " ev.ev_stacksize;
  printf "ev_repr=%s,@ " (repr_string ev);
  ()

let print_event (ev: Instruct.debug_event) =
  if !print_full_events_flag then
    print_ev ev
  else if !print_locations_flag then
    let ls = ev.ev_loc.loc_start in
    let le = ev.ev_loc.loc_end in
    printf "Def %s, File \"%s\", line %d, characters %d-%d:@." 
    ev.ev_defname
    ls.Lexing.pos_fname
      ls.Lexing.pos_lnum (ls.Lexing.pos_cnum - ls.Lexing.pos_bol)
      (le.Lexing.pos_cnum - ls.Lexing.pos_bol);
    if !print_source_flag then
      Show_source.show_point ev true

let print_ev_indexed (ev: Instruct.debug_event)  j =
  printf "@[<2>ev[%d]:{@ " j;
  print_event ev;
  printf "}@]@.";
  ()

let dump_eventlist evl =
  if !print_debug_flag then begin
    printf "length evl=%d@." (List.length evl);
    let j = ref 0 in
    List.iter (fun ev ->
      print_ev_indexed  ev !j;
      j := !j + 1;
      ) evl;
  end

let print_instr ic =
  let pos = currpos ic in
  List.iter print_event (Hashtbl.find_all event_table pos);
  printf "%8d  " (pos / 4);
  let op = inputu ic in
  if op >= Array.length Opnames.names_of_instructions || op < 0
  then (print_string "*** unknown opcode : "; print_int op)
  else print_string names_of_instructions.(op);
  begin try
    let shape = List.assoc op op_shapes in
    if shape <> Nothing then print_string " ";
    match shape with
    | Uint -> print_int (inputu ic)
    | Sint -> print_int (inputs ic)
    | Uint_Uint
       -> print_int (inputu ic); print_string ", "; print_int (inputu ic)
    | Disp -> let p = currpc ic in print_int (p + inputs ic)
    | Uint_Disp
       -> print_int (inputu ic); print_string ", ";
          let p = currpc ic in print_int (p + inputs ic)
    | Sint_Disp
       -> print_int (inputs ic); print_string ", ";
          let p = currpc ic in print_int (p + inputs ic)
    | Getglobal -> print_getglobal_name ic
    | Getglobal_Uint
       -> print_getglobal_name ic; print_string ", "; print_int (inputu ic)
    | Setglobal -> print_setglobal_name ic
    | Primitive -> print_primitive ic
    | Uint_Primitive
       -> print_int(inputu ic); print_string ", "; print_primitive ic
    | Switch
       -> let n = inputu ic in
          let orig = currpc ic in
          for i = 0 to (n land 0xFFFF) - 1 do
            printf "@.        int "; print_int i; print_string " -> ";
            print_int(orig + inputs ic);
          done;
          for i = 0 to (n lsr 16) - 1 do
            printf "@.        tag "; print_int i; print_string " -> ";
            print_int(orig + inputs ic);
          done;
    | Closurerec
       -> let nfuncs = inputu ic in
          let nvars = inputu ic in
          let orig = currpc ic in
          print_int nvars;
          for _i = 0 to nfuncs - 1 do
            print_string ", ";
            print_int (orig + inputs ic);
          done;
    | Pubmet
       -> let tag = inputs ic in
          let _cache = inputu ic in
          print_int tag
    | Nothing -> ()
  with Not_found -> print_string " (unknown arguments)"
  end;
  printf "@.";
;;

(* Disassemble a block of code *)

let print_code ic len =
  start := pos_in ic;
  let stop = !start + len in
  while pos_in ic < stop do print_instr ic done

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

let string_of_crc crc = if !print_crc_flag then Digest.to_hex crc else null_crc

let print_name_crc (name, crco) =
  let crc =
    match crco with
      None -> dummy_crc
    | Some crc -> string_of_crc crc
  in
    printf "\t%s\t%s@." crc name

let print_line name =
  printf "\t%s@." name

let print_required_global id =
  printf "\t%s@." (Ident.name id)

 (* Relocation information 

type reloc_info =
    Reloc_literal of Lambda.structured_constant    (* structured constant *)
  | Reloc_getglobal of Ident.t              (* reference to a global *)
  | Reloc_setglobal of Ident.t              (* definition of a global *)
  | Reloc_primitive of string               (* C primitive number *)

*)
(*
type compilation_unit =
  { cu_name: modname;                   (* Name of compilation unit *)
    mutable cu_pos: int;                (* Absolute position in file *)
    cu_codesize: int;                   (* Size of code block *)
    cu_reloc: (reloc_info * int) list;  (* Relocation information *)
    cu_imports: crcs;                   (* Names and CRC of intfs imported *)
    cu_required_globals: Ident.t list;  (* Compilation units whose
                                           initialization side effects
                                           must occur before this one. *)
    cu_primitives: string list;         (* Primitives declared inside *)
    mutable cu_force_link: bool;        (* Must be linked even if unref'ed *)
    mutable cu_debug: int;              (* Position of debugging info, or 0 *)
    cu_debugsize: int }                 (* Length of debugging info *)
*)
(* Format of a .cmo file:
     magic number (Config.cmo_magic_number)
     absolute offset of compilation unit descriptor
     block of relocatable bytecode
     debugging information if any
     compilation unit descriptor *)

let print_cmo_infos ic cu =
  printf "Unit name: %s@." cu.cu_name;
  if !print_imports_flag then begin
    printf "Interfaces imported:@.";
    List.iter print_name_crc cu.cu_imports;
  end;
  if !print_globals_flag then begin
    printf "Required globals:@.";
    List.iter print_required_global cu.cu_required_globals;
  end;
  printf "Uses unsafe features: ";
  (match cu.cu_primitives with
    | [] -> printf "no@."
    | l  ->
        printf "YES@.";
        printf "Primitives declared in this module:@.";
        List.iter print_line l);
  printf "Force link: %s@." (if cu.cu_force_link then "YES" else "no");
  reloc := cu.cu_reloc;
  if !print_reloc_info_flag then begin
    printf "Relocation information@.";
    List.iter print_reloc cu.cu_reloc;
  end;
  let debug_size = cu.cu_debugsize in
  if !print_debug_flag then
    (printf "debug_size=%u@." debug_size);
  if debug_size > 0 then begin
    if !print_debug_flag then begin
      printf "cu_debug=%u@." cu.cu_debug;
      let in_pos = pos_in ic in
      printf "in_pos=%u@." in_pos;
    end;
    seek_in ic cu.cu_debug;
    let evl = (input_value ic : Instruct.debug_event list) in
    record_events 0 evl;
    let (dirs : string list) = input_value ic in
    if !print_dirs_flag then begin
      printf "#dirs = %d@." (List.length dirs);
      printf "@[<v 2>dirs=";
      List.iter (fun dir -> printf "%s@ " dir) dirs;
      printf "@]";
    end;
    if !print_code_flag then begin
      (* Events will be dumped as part of the code.*)
      seek_in ic cu.cu_pos;
      print_code ic cu.cu_codesize
    end else if !print_debug_flag then begin
      printf "#evl = %d@." (List.length evl);
      dump_eventlist evl
    end
  end

let print_spaced_string s =
  printf " %s" s

  (* Descriptor for libraries *)
(*
type library =
  { lib_units: compilation_unit list;   (* List of compilation units *)
    lib_custom: bool;                   (* Requires custom mode linking? *)
    (* In the following fields the lists are reversed with respect to
       how they end up being used on the command line. *)
    lib_ccobjs: string list;            (* C object files needed for -custom *)
    lib_ccopts: string list;            (* Extra opts to C compiler *)
    lib_dllibs: string list }           (* DLLs needed *)
*)
(* Format of a .cma file:
     magic number (Config.cma_magic_number)
     absolute offset of library descriptor
     object code for first library member
     ...
     object code for last library member
     library descriptor *)

let print_cma_infos ic (lib : Cmo_format.library) =
  printf "Force custom: %s@." (if lib.lib_custom then "YES" else "no");
  printf "Extra C object files:";
  (* PR#4949: print in linking order *)
  List.iter print_spaced_string (List.rev lib.lib_ccobjs);
  printf "@.Extra C options:";
  List.iter print_spaced_string (List.rev lib.lib_ccopts);
  printf "@.";
  printf "Extra dynamically-loaded libraries:";
  List.iter print_spaced_string (List.rev lib.lib_dllibs);
  printf "@.";
  List.iter (print_cmo_infos ic) lib.lib_units

let string_of_pers_flags fl = 
  match fl with 
    Cmi_format.Rectypes -> "Rectypes"
  | Alerts al -> "Alerts"
  | Cmi_format.Opaque -> "Opaque"
  | Unsafe_string -> "Unsafe_string"

let print_cmi_infos cmi =
  printf "Unit name: %s@." cmi.Cmi_format.cmi_name;
  printf "Flags:@.";
  List.iter (fun flag -> printf "%s@ " (string_of_pers_flags flag)) 
  cmi.cmi_flags;

  if !print_imports_flag then begin
    printf "Interfaces imported:@.";
    List.iter print_name_crc cmi.Cmi_format.cmi_crcs;
  end;
  printf "Signatures:@.";
  Xprinttyp.signature std_formatter cmi.cmi_sign;
  printf "@."

let print_cmt_infos cmt =
  let open Cmt_format in
  printf "Cmt unit name: %s@." cmt.cmt_modname;
  printf "Cmt interfaces imported:@.";
  List.iter print_name_crc cmt.cmt_imports;
  printf "Source file: %s@."
         (match cmt.cmt_sourcefile with None -> "(none)" | Some f -> f);
  printf "Compilation flags:";
  Array.iter print_spaced_string cmt.cmt_args;
  printf "@.Load path:";
  List.iter print_spaced_string cmt.cmt_loadpath;
  printf "@.";
  printf "cmt interface digest: %s@."
    (match cmt.cmt_interface_digest with
     | None -> ""
     | Some crc -> string_of_crc crc)

let print_general_infos name crc defines cmi cmx =
  printf "Name: %s@." name;
  printf "CRC of implementation: %s@." (string_of_crc crc);
  printf "Globals defined:@.";
  List.iter print_line defines;
  printf "Interfaces imported:@.";
  List.iter print_name_crc cmi;
  printf "Implementations imported:@.";
  List.iter print_name_crc cmx

open Cmx_format
open Cmxs_format

let print_cmx_infos (ui, crc) =
  print_general_infos
    ui.ui_name crc ui.ui_defines ui.ui_imports_cmi ui.ui_imports_cmx;
  begin match ui.ui_export_info with
  | Clambda approx ->
    if !print_approx_flag then begin
      printf "Clambda approximation:@.";
      Format.fprintf Format.std_formatter "  %a@." Printclambda.approx approx
    end else
      Format.printf "Clambda unit@.";
  | Flambda export ->
    if !print_approx_flag || !print_code_flag then
      printf "Flambda export information:@."
    else
      printf "Flambda unit@.";
    if !print_approx_flag then begin
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
    if !print_code_flag then
      Format.printf "functions@ %a@.@."
        Export_info.print_functions export
  end;
  let pr_funs _ fns =
    List.iter (fun arity -> printf " %d" arity) fns in
  printf "Currying functions:%a@." pr_funs ui.ui_curry_fun;
  printf "Apply functions:%a@." pr_funs ui.ui_apply_fun;
  printf "Send functions:%a@." pr_funs ui.ui_send_fun;
  printf "Force link: %s@." (if ui.ui_force_link then "YES" else "no")

let print_cmxa_infos (lib : Cmx_format.library_infos) =
  printf "Extra C object files:";
  List.iter print_spaced_string (List.rev lib.lib_ccobjs);
  printf "@.Extra C options:";
  List.iter print_spaced_string (List.rev lib.lib_ccopts);
  printf "@.";
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

let p_title title = printf "%s:@." title

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

(* Read the primitive table from an executable *)

let read_primitive_table ic len =
  let p = really_input_string ic len in
  String.split_on_char '\000' p |> List.filter ((<>) "") |> Array.of_list

let dump_byte ic =
  objfile := false;
  Bytesections.read_toc ic;
  let toc = Bytesections.toc () in
  let toc = List.sort Stdlib.compare toc in
  (* The sections are CRCS, DLLS, DLPT, PRIM, SYMB, DBUG, and CODE. *)
  if !print_imports_flag then
  begin try 
    ignore (Bytesections.seek_section ic "CRCS");
    p_section
      "Imported units"
      (input_value ic : (string * Digest.t option) list)
    with Not_found -> printf "No imported units"
  end;

  if !print_dlls_flag then
  begin try 
      let len = Bytesections.seek_section ic "DLLS" in
      printf "DLLs len=%d@." len;
      if len > 0 then begin
        p_list "Used DLLs" print_line (input_stringlist ic len);
        printf "After p_list@.";
      end
    with Not_found -> printf "No used DLLs";
  end;
 
  if !print_dll_paths_flag then
  begin try 
    let len = Bytesections.seek_section ic "DLPT" in
    printf "DLPT len=%d@." len;
    if len > 0 then begin
      p_list "Additional DLL paths" print_line (input_stringlist ic len);
      printf "After p_list@.";
    end
  with Not_found -> printf "No additional DLL paths";
  end;
  
  let prim_size = Bytesections.seek_section ic "PRIM" in
  primitives := read_primitive_table ic prim_size;
  if !print_primitives_flag then begin
    printf "prim_size=%d@." prim_size;
    if prim_size > 0 then begin
      for i = 0 to Array.length !primitives - 1 do
        printf "primitive[%d] = %s@." i !primitives.(i)
      done
    end;
  end;

  ignore(Bytesections.seek_section ic "DATA");
  let init_data = (input_value ic : Obj.t array) in
  globals := Array.make (Array.length init_data) Empty;
  for i = 0 to Array.length init_data - 1 do
    !globals.(i) <- Constant (init_data.(i))
  done;
  ignore(Bytesections.seek_section ic "SYMB");
  let sym_table = (input_value ic : Symtable.global_map) in
  Symtable.iter_global_map
    (fun id pos -> 
      !globals.(pos) <- Global id
      ) sym_table;
  if !print_globals_flag then begin
    printf "Globals table:@.";
    for i = 0 to Array.length init_data - 1 do
      printf "global[%d] = " i;
      print_global !globals.(i);
      printf "@."
    done;
  end;

  begin try
    ignore (Bytesections.seek_section ic "DBUG");
    let num_eventlists = input_binary_int ic in
    if !print_debug_flag then
      (printf "num_eventlists=%d@." num_eventlists);
    for _i = 1 to num_eventlists do
      let orig = input_binary_int ic in
      if !print_debug_flag then
        (printf "orig=%d@." orig);
      let evl = (input_value ic : Instruct.debug_event list) in
      record_events orig evl;
      let (dirs : string list) = input_value ic in
      if !print_dirs_flag then begin
        printf "@[<v 2>Debug directories=@,";
        List.iter (fun dir -> printf "%s@ " dir) dirs;
        printf "@]@.";
      end;
    done
  with Not_found -> printf "No debug information";
  end;
  let code_size = Bytesections.seek_section ic "CODE" in
  if !print_code_flag then
    print_code ic code_size
  else ()

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
     "Wrong magic number:@.\
      this tool only supports object files produced by compiler version@.\
      \t%s@.\
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
    | Cmi -> 
        let cmi = Cmi_format.input_cmi ic in
        print_cmi_infos cmi
    | Cmt ->
       close_in ic;
       let cmi, cmt = Cmt_format.read filename in
       begin match cmi with
         | None -> ()
         | Some cmi ->
            print_cmi_infos cmi
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

let print_all () =
  print_approx_flag := true;
  print_code_flag := true;
  print_crc_flag := true;
  print_debug_flag := true;
  print_dirs_flag := true;
  print_dlls_flag := true;
  print_dll_paths_flag := true;
  print_full_events_flag := true;
  print_globals_flag := true;
  print_imports_flag := true;
  print_locations_flag := true;
  print_primitives_flag := true;
  print_reloc_info_flag := true;
  ()

let print_none () =
  print_approx_flag := false;
  print_code_flag := false;
  print_crc_flag := false;
  print_debug_flag := false;
  print_dirs_flag := false;
  print_dlls_flag := false;
  print_dll_paths_flag := false;
  print_full_events_flag := false;
  print_globals_flag := false;
  print_imports_flag := false;
  print_locations_flag := false;
  print_primitives_flag := false;
  print_reloc_info_flag := false;
  ()

let arg_list = [
  "-approx", Arg.Set print_approx_flag,
    " Print module approximation information";
  "-no-approx", Arg.Clear print_approx_flag,
    " Do not print module approximation information";
  "-code", Arg.Set print_code_flag,
    " Print bytecode or code from exported flambda functions";
  "-no-code", Arg.Clear print_code_flag,
    " Do not print code or code from exported flambda functions";
  "-crc", Arg.Set print_crc_flag, " Print a CRC for imported interfaces";
  "-no-crc", Arg.Clear print_crc_flag, " Print a null CRC for imported interfaces";
  "-debug", Arg.Set print_debug_flag,
    " Print debug information";
  "-no-debug", Arg.Clear print_debug_flag,
    " Do not print debug information";
  "-dirs", Arg.Set print_dirs_flag,
    " Print source directories from the debug information";
  "-no-dirs", Arg.Clear print_dirs_flag,
    " Do not print source directories from the debug information";
  "-dlls", Arg.Set print_dlls_flag,
    " Print DLLs used";
  "-no-dlls", Arg.Clear print_dlls_flag,
    " Do not print DLLs used";
  "-dll-paths", Arg.Set print_dll_paths_flag,
    " Print additional DLL paths used";
  "-no-dll-paths", Arg.Clear print_dll_paths_flag,
    " Do not print additional DLL paths used";
  "-full-events", Arg.Set print_full_events_flag,
    " Print full debug events";
  "-no-full-events", Arg.Clear print_full_events_flag,
    " If printing debug information, print only location of events, if locations are requested";
  "-globals", Arg.Set print_globals_flag,
    " Print globals table";
  "-no-globals", Arg.Clear print_globals_flag,
    " Do not print globals table";
  "-imports", Arg.Set print_imports_flag,
    " Print imports";
  "-no-imports", Arg.Clear print_imports_flag,
    " Do not print imports";
  "-locations", Arg.Set print_locations_flag,
    " Print locations of debug events";
  "-no-locations", Arg.Clear print_locations_flag,
    " Do not print locations of debug events";
  "-primitives", Arg.Set print_primitives_flag,
    " Print primitives used table";
  "-no-primitives", Arg.Clear print_primitives_flag,
    " Do not print primitives used table";
  "-reloc", Arg.Set print_reloc_info_flag, " Print relocation information for the code";
  "-no-reloc", Arg.Clear print_reloc_info_flag, " Do not print relocation information for the code";
  "-source", Arg.Set print_source_flag, " Print source with code";
  "-no-source", Arg.Clear print_source_flag, " Do not print source with code";
  "-all", Arg.Unit print_all,
    "Enable all print options";
  "-none", Arg.Unit print_none,
    "Disable all print options";
  "-args", Arg.Expand Arg.read_arg,
     "<file> Read additional newline separated command line arguments @.\
     \      from <file>";
  "-args0", Arg.Expand Arg.read_arg0,
     "<file> Read additional NUL separated command line arguments from @.\
     \      <file>";
]
let arg_usage =
   Printf.sprintf "%s [OPTIONS] FILES : give information on files" Sys.argv.(0)

let main() =
  Arg.parse_expand arg_list dump_obj arg_usage;
  exit 0

let _ = main ()
