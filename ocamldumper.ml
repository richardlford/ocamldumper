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
open Lambda
open Format
open Opcodes
open Opnames



(* Command line options *)
let the_filename = ref ""
let the_realfile = ref ""
let print_approx_flag = ref true
let print_code_flag = ref true
let print_crc_flag = ref true
let print_debug_flag = ref true
let print_description_flag = ref true
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

(* If true, only show identifiers in the computational environment *)
let comp_env_filter_flag = ref true

(* String from which a regular expression is formed to filter
   output to the given module. *)
let module_filter_string = ref ""
let module_filter_re: Str.regexp option ref = ref None 

let is_matching_module mdle =
  match !module_filter_re with
  | None -> true
  | Some re -> Str.string_match re mdle 0

(* Extra path to search for source files. *)
let extra_path = ref ([] : string list)

(* Source file we want to examine *)
let desired_source_filename = ref ""

(* List of directories to act as workspace roots. *)
let workspace_roots: string list ref = ref []

(* Tell if included in file filter *)
let keep_file = ref true

let workspace_marker = "/workspace_root"
let workspace_marker_slash = "/workspace_root/"

let workspace_marker_len = String.length workspace_marker
let build_re = Str.regexp {|\(.*\)/_build/.*|}

module Magic_number = Misc.Magic_number

let find_workspace_roots () =
  printf "find_workspace_roots: entered.@.";
  if Str.string_match build_re !the_realfile 0 then begin
    printf "Got match.@.";
    let root = Str.matched_group 1 !the_realfile in
    printf "root=%s@." root;
    workspace_roots := root :: !workspace_roots
  end else begin
    printf "Workspace root not found";
    workspace_roots := ["/workspace_root"]
  end
    
let has_workspace_marker dir_name =
  (dir_name = workspace_marker) ||
   String.starts_with ~prefix: workspace_marker_slash dir_name

(* Because we might have multiple workspace roots, a single
   filename might expand into multiple filenames. *)
let expand_workspace_root dir_name =
  if not (has_workspace_marker dir_name) then [dir_name]
  else begin
    if List.length !workspace_roots = 0 then
      find_workspace_roots ();
    let stem = String.sub dir_name workspace_marker_len 
              (String.length dir_name - workspace_marker_len) in
    List.map (fun root -> root ^ stem) !workspace_roots
  end

let add_expanded_dir dir_name =
  let expanded = expand_workspace_root dir_name in
  List.iter Load_path.add_dir expanded

let check_file fname =
  if !desired_source_filename <> "" then begin
    (* Only change for non-none filemames *)
    if fname <>  "_none_" then
      keep_file := (fname = !desired_source_filename)
  end

let is_desired_loc (loc: Location.t) =
  let desired = !desired_source_filename in
  if String.equal desired "" then true
  else begin
    let ls = loc.loc_start in
    let filename = ls.pos_fname in
    String.equal desired filename
  end

let () =
  Load_path.reset ()


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

let rec print_struct_const ppf = function
    Const_base(Const_int i) -> fprintf ppf "%d" i
  | Const_base(Const_float f) -> print_float f
  | Const_base(Const_string (s, _, _)) -> fprintf ppf "%S" s
  | Const_immstring s -> fprintf ppf "%S" s
  | Const_base(Const_char c) -> fprintf ppf "%C" c
  | Const_base(Const_int32 i) -> fprintf ppf "%ldl" i
  | Const_base(Const_nativeint i) -> fprintf ppf "%ndn" i
  | Const_base(Const_int64 i) -> fprintf ppf "%LdL" i
  | Const_block(tag, args) ->
      fprintf ppf "<%d>" tag;
      begin match args with
        [] -> ()
      | [a1] ->
          fprintf ppf "("; print_struct_const ppf a1; fprintf ppf ")"
      | a1::al ->
          fprintf ppf "("; print_struct_const ppf a1;
          List.iter (fun a -> fprintf ppf ", "; print_struct_const ppf a) al;
          fprintf ppf ")"
      end
  | Const_float_array a ->
      fprintf ppf "[|";
      List.iter (fun f -> print_float f; fprintf ppf "; ") a;
      fprintf ppf "|]"

(* Print an obj *)

let same_custom x y =
  Obj.field x 0 = Obj.field (Obj.repr y) 0

let rec print_obj ppf x =
  if Obj.is_block x then begin
    let tag = Obj.tag x in
    if tag = Obj.string_tag then
        fprintf ppf "%S" (Obj.magic x : string)
    else if tag = Obj.double_tag then
        fprintf ppf "%.12g" (Obj.magic x : float)
    else if tag = Obj.double_array_tag then begin
        let a = (Obj.magic x : floatarray) in
        fprintf ppf "[|";
        for i = 0 to Array.Floatarray.length a - 1 do
          if i > 0 then fprintf ppf ", ";
          fprintf ppf "%.12g" (Array.Floatarray.get a i)
        done;
        fprintf ppf "|]"
    end else if tag = Obj.custom_tag && same_custom x 0l then
        fprintf ppf "%ldl" (Obj.magic x : int32)
    else if tag = Obj.custom_tag && same_custom x 0n then
        fprintf ppf "%ndn" (Obj.magic x : nativeint)
    else if tag = Obj.custom_tag && same_custom x 0L then
        fprintf ppf "%LdL" (Obj.magic x : int64)
    else if tag < Obj.no_scan_tag then begin
        fprintf ppf "<%d>" (Obj.tag x);
        match Obj.size x with
          0 -> ()
        | 1 ->
            fprintf ppf "("; print_obj ppf (Obj.field x 0); fprintf ppf ")"
        | n ->
            fprintf ppf "("; print_obj ppf (Obj.field x 0);
            for i = 1 to n - 1 do
              fprintf ppf ", "; print_obj ppf (Obj.field x i)
            done;
            fprintf ppf ")"
    end else
        fprintf ppf "<tag %d>" tag
  end else
    fprintf ppf "%d" (Obj.magic x : int)

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

let print_global ppf item =
  match item with
    Global id -> pp_print_string ppf (Ident.name id)
  | Constant obj -> print_obj ppf obj
  | _ -> pp_print_string ppf "???"

let print_getglobal_name ppf ic =
  if !objfile then begin
    begin try
      match find_reloc ic with
          Reloc_getglobal id -> pp_print_string ppf (Ident.name id)
        | Reloc_literal sc -> print_struct_const ppf sc
        | _ -> pp_print_string ppf "<wrong reloc>"
    with Not_found ->
      pp_print_string ppf "<no reloc>"
    end;
    ignore (inputu ic);
  end
  else begin
    let n = inputu ic in
    if n >= Array.length !globals || n < 0
    then pp_print_string ppf "<global table overflow>"
    else print_global ppf !globals.(n) 
  end

let print_setglobal_name ppf ic =
  if !objfile then begin
    begin try
      match find_reloc ic with
        Reloc_setglobal id -> pp_print_string ppf (Ident.name id)
      | _ -> pp_print_string ppf "<wrong reloc>"
    with Not_found ->
      pp_print_string ppf "<no reloc>"
    end;
    ignore (inputu ic);
  end
  else begin
    let n = inputu ic in
    if n >= Array.length !globals || n < 0
    then pp_print_string ppf "<global table overflow>"
    else match !globals.(n) with
           Global id -> pp_print_string ppf (Ident.name id)
         | _ -> pp_print_string ppf "???"
  end

let print_primitive ppf ic =
  if !objfile then begin
    begin try
      match find_reloc ic with
        Reloc_primitive s -> pp_print_string ppf s
      | _ -> pp_print_string ppf "<wrong reloc>"
    with Not_found ->
      pp_print_string ppf "<no reloc>"
    end;
    ignore (inputu ic);
  end
  else begin
    let n = inputu ic in
    if n >= Array.length !primitives || n < 0
    then pp_print_int ppf n
    else pp_print_string ppf !primitives.(n)
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

(* Shape and description of each opcode *)
let op_info = [
  opACC0, (Nothing, "accu = sp[0]");
  opACC1, (Nothing, "accu = sp[1]");
  opACC2, (Nothing, "accu = sp[2]");
  opACC3, (Nothing, "accu = sp[3]");
  opACC4, (Nothing, "accu = sp[4]");
  opACC5, (Nothing, "accu = sp[5]");
  opACC6, (Nothing, "accu = sp[6]");
  opACC7, (Nothing, "accu = sp[7]");
  opACC, (Uint, "n=> accu = sp[n]");
  opPUSH, (Nothing, "push accu");
  opPUSHACC0, (Nothing, "push accu; accu = sp[0]");
  opPUSHACC1, (Nothing, "push accu; accu = sp[1]");
  opPUSHACC2, (Nothing, "push accu; accu = sp[2]");
  opPUSHACC3, (Nothing, "push accu; accu = sp[3]");
  opPUSHACC4, (Nothing, "push accu; accu = sp[4]");
  opPUSHACC5, (Nothing, "push accu; accu = sp[5]");
  opPUSHACC6, (Nothing, "push accu; accu = sp[6]");
  opPUSHACC7, (Nothing, "push accu; accu = sp[7]");
  opPUSHACC, (Uint, "n=> push accu; accu = sp[n]");
  opPOP, (Uint, "n=> pop  items from the stack");
  opASSIGN, (Uint, "n=> sp[n] = accu; accu = ()");
  opENVACC1, (Nothing, "accu = env(1)");
  opENVACC2, (Nothing, "accu = env(2)");
  opENVACC3, (Nothing, "accu = env(3)");
  opENVACC4, (Nothing, "accu = env(4)");
  opENVACC, (Uint, "n=> accu = env(n)");
  opPUSHENVACC1, (Nothing, "push accu; accu = env(1)");
  opPUSHENVACC2, (Nothing, "push accu; accu = env(2)");
  opPUSHENVACC3, (Nothing, "push accu; accu = env(3)");
  opPUSHENVACC4, (Nothing, "push accu; accu = env(4)");
  opPUSHENVACC, (Uint, "push accu; accu = env(*pc++)");
  opPUSH_RETADDR, (Disp, "n=> push pc+n; push env; push extra_args");
  opAPPLY, (Uint, "n=> extra_args = n - 1; pc = Code_val(accu); env = accu;");
  opAPPLY1, (Nothing, "arg1 = pop; push extra_args, env, pc, arg1; pc = Code_val(accu); env = accu; extra_args = 0");
  opAPPLY2, (Nothing, "arg1,arg2 = pops; push extra_args, env, pc, arg2, arg1; pc = Code_val(accu); env = accu; extra_args = 1");
  opAPPLY3, (Nothing, "arg1,arg2,arg3 = pops; push extra_args, env, pc, arg3, arg2, arg1; pc = Code_val(accu); env = accu; extra_args = 2");
  opAPPTERM, (Uint_Uint, "n,s=> sp[0..s-1]=sp[0..n-1];pc = Code_val(accu); env = accu; extra_args += n-1");
  opAPPTERM1, (Uint, "n=> arg1=pop;pop n-1 items; push arg1;pc = Code_val(accu); env = accu");
  opAPPTERM2, (Uint, "n=> arg1,arg2=pops;pop n-2 items; push arg2,arg1;pc = Code_val(accu); env = accu;extra_args++");
  opAPPTERM3, (Uint, "n=> arg1,arg2,arg3=pops;pop n-3 items; push arg3,arg2,arg1;pc = Code_val(accu); env = accu;extra_args+=2");
  opRETURN, (Uint, "n=> pop n elements; if(extra_args> 0){extra_args--;pc=Code_val(accu);env = accu}else{pc,env,extra_args=pops}");
  opRESTART, (Nothing, "n=size(env);push env(n-1..3);env=env(2);extra_args+=n-3");
  opGRAB, (Uint, "n=> if(extra_args>=n){extra_args-=n}else{m=1+extra_args;accu=closure with m args, field2=env,code=pc-3, args popped}");
  opCLOSURE, (Uint_Disp, "n,ofs=> if(n>0){push accu};accu=closure of n+1 elements;Code_val(acc)=pc+ofs;arity=0;env offset=2");
  opCLOSUREREC, (Closurerec, "nvar,[f...]=> accu=closure for f0 and Infix closures for f1..., all sharing the nvars from accu and stack;push closures");
  opOFFSETCLOSUREM3, (Nothing, "accu=&env[-3]");
  opOFFSETCLOSURE0, (Nothing, "accu=env");
  opOFFSETCLOSURE3, (Nothing, "accu=*env[3]");
  opOFFSETCLOSURE, (Sint, "n=> accu=&env[n]");  (* was Uint *)
  opPUSHOFFSETCLOSUREM3, (Nothing, "push accu;accu=&env[-3]");
  opPUSHOFFSETCLOSURE0, (Nothing, "push accu;accu=env");
  opPUSHOFFSETCLOSURE3, (Nothing, "push accu;accu=*env[3]");
  opPUSHOFFSETCLOSURE, (Sint, "n=> push accu;accu=&env[n]"); (* was Nothing *)
  opGETGLOBAL, (Getglobal, "n=> accu=global[n]");
  opPUSHGETGLOBAL, (Getglobal, "n=> push accu; accu=global[n]");
  opGETGLOBALFIELD, (Getglobal_Uint, "n,p=> accu=global[n][p]");
  opPUSHGETGLOBALFIELD, (Getglobal_Uint, "n,p=> push accu;accu=global[n][p]");
  opSETGLOBAL, (Setglobal, "n=> global[n]=accu; accu=()");
  opATOM0, (Nothing, "accu = Atom(0)");
  opATOM, (Uint, "n=> accu = Atom(n)");
  opPUSHATOM0, (Nothing, "push accu; accu = Atom(0)");
  opPUSHATOM, (Uint, "n=> push accu; accu = Atom(n)");
  opMAKEBLOCK, (Uint_Uint, "n,t=> accu=n-element block with tag t, elements from accu and popped stack");
  opMAKEBLOCK1, (Uint, "t=> accu=1-element block, tag t, element from accu");
  opMAKEBLOCK2, (Uint, "t=> accu=2-element block, tag t, elements from accu and pop");
  opMAKEBLOCK3, (Uint, "t=> accu=3-element block, tag t, elements from accu and popped stack");
  opMAKEFLOATBLOCK, (Uint, "n=> n-element float block, elements from accu and popped stack");
  opGETFIELD0, (Nothing, "accu = accu[0]");
  opGETFIELD1, (Nothing, "accu = accu[1]");
  opGETFIELD2, (Nothing, "accu = accu[2]");
  opGETFIELD3, (Nothing, "accu = accu[3]");
  opGETFIELD, (Uint, "n=> accu = accu[n]");
  opGETFLOATFIELD, (Uint, "n=> accu=Double Block with DoubleField(accu, n)");
  opSETFIELD0, (Nothing, "accu[0] = pop; accu=()");
  opSETFIELD1, (Nothing, "accu[1] = pop; accu=()");
  opSETFIELD2, (Nothing, "accu[2] = pop; accu=()");
  opSETFIELD3, (Nothing, "accu[3] = pop; accu=()");
  opSETFIELD, (Uint, "n=> accu[n] = pop; accu=()");
  opSETFLOATFIELD, (Uint, "DoubleField(accu, n) = pop; accu=()");
  opVECTLENGTH, (Nothing, "accu = size of block in accu (/2 if Double array)");
  opGETVECTITEM, (Nothing, "n=pop; accu=accu[n]");
  opSETVECTITEM, (Nothing, "n=pop;v=pop;accu[n]=v");
  opGETSTRINGCHAR, (Nothing, "n=pop; accu = nth unsigned char of accu string");
  opGETBYTESCHAR, (Nothing, "n=pop; accu = nth unsigned char of accu string");
  opSETBYTESCHAR, (Nothing, "n=pop;v=pop; nth unsigned char of accu set to v");
  opBRANCH, (Disp, "ofs=> pc += ofs");
  opBRANCHIF, (Disp, "ofs=> if(accu != false){pc += ofs}");
  opBRANCHIFNOT, (Disp, "ofs=> if(accu == false){pc += ofs}");
  opSWITCH, (Switch, "n=> tab=pc;szt=n>>16;szl=n&0xffff;if(Is_block(accu)){ix=Tag_val(accu);pc += tab[szl+ix]}else{pc += tab[accu]");
  opBOOLNOT, (Nothing, "accu = not accu");
  opPUSHTRAP, (Disp, "ofs=> push extra_args, env, trap_sp_offset, pc+ofs");
  opPOPTRAP, (Nothing, "pop;trap_sp_offset=pop;pop;pop");
  opRAISE, (Nothing, "if(no frame){stop}else{sp=trapsp;pop pc,trapsp,env,extra_args}");
  opCHECK_SIGNALS, (Nothing, "Handle signals, if any. accu not preserved.");
  opC_CALL1, (Primitive, "p=> accu=primitive(p)(accu)");
  opC_CALL2, (Primitive, "p=> accu=primitive(p)(accu, pop)");
  opC_CALL3, (Primitive, "p=> accu=primitive(p)(accu, pop, pop)");
  opC_CALL4, (Primitive, "p=> accu=primitive(p)(accu, pop, pop, pop)");
  opC_CALL5, (Primitive, "p=> accu=primitive(p)(accu, pop, pop, pop, pop)");
  opC_CALLN, (Uint_Primitive, "n,p=> accu=primitive(p)(accu, (n-1)-pops");
  opCONST0, (Nothing, "accu = 0");
  opCONST1, (Nothing, "accu = 1");
  opCONST2, (Nothing, "accu = 2");
  opCONST3, (Nothing, "accu = 3");
  opCONSTINT, (Sint, "n=> accu = n");
  opPUSHCONST0, (Nothing, "push accu; accu = 0");
  opPUSHCONST1, (Nothing, "push accu; accu = 1");
  opPUSHCONST2, (Nothing, "push accu; accu = 2");
  opPUSHCONST3, (Nothing, "push accu; accu = 3");
  opPUSHCONSTINT, (Sint, "n=> push accu; accu = n");
  opNEGINT, (Nothing, "accu = -accu");
  opADDINT, (Nothing, "accu = accu + pop");
  opSUBINT, (Nothing, "accu = accu - pop");
  opMULINT, (Nothing, "accu = accu * pop");
  opDIVINT, (Nothing, "accu = accu / pop.");
  opMODINT, (Nothing, "accu = accu % pop");
  opANDINT, (Nothing, "accu = accu & pop");
  opORINT, (Nothing, "accu = accu | pop");
  opXORINT, (Nothing, "accu = accu ^ pop");
  opLSLINT, (Nothing, "accu = accu << pop");
  opLSRINT, (Nothing, "accu = (unsigned)accu >> pop");
  opASRINT, (Nothing, "accu = (signed)accu >> pop ");
  opEQ, (Nothing, "accu = accu == pop");
  opNEQ, (Nothing, "accu = accu != pop");
  opLTINT, (Nothing, "accu = accu < pop");
  opLEINT, (Nothing, "accu = accu <= pop");
  opGTINT, (Nothing, "accu = accu > pop");
  opGEINT, (Nothing, "accu = accu >= pop");
  opOFFSETINT, (Sint, "ofs=> accu += ofs");
  opOFFSETREF, (Sint, "ofs=> accu[0] += ofs");
  opISINT, (Nothing, "accu = Val_long(accu & 1)");
  opGETMETHOD, (Nothing, "x=pop;y=x[0];accu = y[accu]");
  opGETDYNMET, (Nothing, "object=sp[0];accu=method matching tag in object's method table");
  opGETPUBMET, (Pubmet, "tag,cache=> object=accu;methods=object[0];push object;accu=method matching tag in methods;");
  opBEQ, (Sint_Disp, "val,ofs=> val == (signed)accu){pc += ofs}");
  opBNEQ, (Sint_Disp, "val,ofs=> if(val != (signed)accu){pc += ofs}");
  opBLTINT, (Sint_Disp, "val,ofs=> if(val < (signed)accu){pc += ofs}");
  opBLEINT, (Sint_Disp, "val,ofs=> if(val <= (signed)accu){pc += ofs}");
  opBGTINT, (Sint_Disp, "val,ofs=> if(val > (signed)accu){pc += ofs}");
  opBGEINT, (Sint_Disp, "val,ofs=> if(val >= (signed)accu){pc += ofs}");
  opULTINT, (Nothing, "accu < (unsigned)pop");
  opUGEINT, (Nothing, "accu >= (unsigned)pop");
  opBULTINT, (Uint_Disp, "val,ofs=> if(val < (unsigned)accu){pc += ofs}");
  opBUGEINT, (Uint_Disp, "val,ofs=> if(val >= (unsigned)accu){pc += ofs}");
  opSTOP, (Nothing, "Stop interpreting, return accu");
  opEVENT, (Nothing, "if(--caml_event_count==0){send event message to debugger}");
  opBREAK, (Nothing, "Send break message to debugger");
  opRERAISE, (Nothing, "Like Raise, but backtrace slightly different");
  opRAISE_NOTRACE, (Nothing, "Raise but do not record backtrace.");
];;

(* Dump relocation info *)

let print_reloc (info, pos) =
  printf "    %d    (%d)    " pos (pos/4);
  match info with
    Reloc_literal sc -> print_struct_const std_formatter sc; printf "@."
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

let in_comp_env (ev: Instruct.debug_event) (id: Ident.t) =
  if not !comp_env_filter_flag then true else begin
    let ce : Instruct.compilation_env = ev.ev_compenv in
    let stack : int Ident.tbl = ce.ce_stack in
    let heap : int Ident.tbl = ce.ce_heap in
    let recs : int Ident.tbl = ce.ce_rec in
    try ignore (Ident.find_same id stack); true;
    with Not_found -> 
    try ignore (Ident.find_same id heap); true;
    with Not_found -> 
    try ignore (Ident.find_same id recs); true;
    with Not_found -> false
end

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
      Location.print_loc std_formatter loc;
    end
  end

let print_summary_item ev summary =
  match summary with
  | Env.Env_empty ->
      () (*print_summary_string "Env_empty" "" *)
  | Env_value (s, id, vd) ->
    let loc = vd.val_loc in
      if not (is_desired_loc loc) then ()
      else if not (in_comp_env ev id) then ()
      else begin
        printf "@[<hov 2>";
        (* print_summary_id "Env_value" id; *)
        let buf = Buffer.create 100 in
        let ppf = Format.formatter_of_buffer buf in
        Xprinttyp.value_description id ppf vd;
        fprintf ppf "@?" ;
        let bcontent = Buffer.contents buf in
        printf "%s;@ " bcontent;
        myprint_loc loc;
        let num_atts = List.length vd.val_attributes in
        if num_atts > 0 then begin
          printf ",@ ";
          printf "#atts=%d@ " num_atts
        end;
        printf "@]@;"
      end
  | Env_type (s, id, td) ->
    let loc = td.type_loc in
      if not (is_desired_loc loc) then ()
      else begin
        printf "@[<hov 2>";
        (* print_summary_id "Env_type" id; *)
        Xprinttyp.type_declaration id std_formatter td;
        myprint_loc loc;
        printf "@]@;";
      end
  | Env_extension (s, id, ec) ->
    let loc = ec.ext_loc in
      if not (is_desired_loc loc) then ()
      else begin
        printf "@[<hov 2>";
        (* print_summary_id "Env_extension" id; *)
        Xprinttyp.extension_constructor id std_formatter ec;
        myprint_loc ec.ext_loc;
        printf "@]@;";
      end
  | Env_module (s, id, mp, md) ->
      if not !comp_env_filter_flag then
        print_summary_id "Env_module" id;
  | Env_modtype (s, id, md) ->
      print_summary_id "Env_modtype" id;
      Xprinttyp.modtype_declaration id std_formatter md
  | Env_class (s, id, cd) ->
      print_summary_id "Env_class" id
  | Env_cltype (s, id, ctd) ->
      print_summary_id "Env_cltype" id
  | Env_open (s, p) ->
      if not !comp_env_filter_flag then
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
      if not !comp_env_filter_flag then begin
        print_summary_string "Env_value_unbound" 
        (String.concat " " [n; "reason"])
      end
  | Env_module_unbound (s, n, r) ->
      print_summary_string "Env_module_unbound" 
      (String.concat " " [n; "reason"])

let rec print_summary ev summary =
  print_summary_item ev summary;
  match next_summary summary with
  | None -> ()
  | Some s -> print_summary ev s

let print_ident_tbl  (title: string) (tbl: int Ident.tbl) =
  if tbl = Ident.empty then begin
    printf "%s = empty@ " title
  end else begin
    printf "@[<2>%s {@ " title;
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
    printf "@[<2>ev_compenv{@ ";
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

(* If there is a non-trivial substitution, get the summary of the
   substituted environment. *)
let get_substituted_summary (ev: Instruct.debug_event) =
  let summary = ev.ev_typenv in
  let subst = ev.ev_typsubst in
  if subst = Subst.identity then
    (* No substitution *)
    summary
  else begin
    let env2 = Envaux.env_from_summary summary subst in
    let summary2 = Env.summary env2 in
    summary2
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
  printf "pc=%d(=4*%d),@ " ev.Instruct.ev_pos (ev.Instruct.ev_pos/4 );
  printf "ev_module=%s" ev.Instruct.ev_module;
  myprint_loc ev.ev_loc;
  printf ",@ ev_kind=%s,@ " (kind_string ev);
  printf "ev_defname=%s,@ " ev.ev_defname;
  printf "ev_info=%s,@ " (info_string ev);
  printf "ev_typenv={@;@[";
  print_summary ev (get_substituted_summary ev);
  printf "}@;@]@.";
  print_comp_env ev.ev_compenv;
  print_subst "ev_typsubst" ev.ev_typsubst;
  printf "ev_stacksize=%d,@ " ev.ev_stacksize;
  printf "ev_repr=%s,@ " (repr_string ev);
  ()

let print_event (ev: Instruct.debug_event) =
  let ls = ev.ev_loc.loc_start in
  let fname = ls.Lexing.pos_fname in
  check_file fname;
  if !keep_file && is_matching_module ev.ev_module then begin
    if !print_full_events_flag then
      print_ev ev
    else if !print_locations_flag then
      let le = ev.ev_loc.loc_end in
      printf "Def %s, File \"%s\", line %d, characters %d-%d:@." 
      ev.ev_defname
      fname
        ls.Lexing.pos_lnum (ls.Lexing.pos_cnum - ls.Lexing.pos_bol)
        (le.Lexing.pos_cnum - ls.Lexing.pos_bol);
      if !print_source_flag then
        Show_source.show_point ev true
  end


let print_ev_indexed (ev: Instruct.debug_event)  j =
  if is_matching_module ev.ev_module then begin
    printf "@[<2>ev[%d]:{@ " j;
    print_event ev;
    printf "}@]@.";
    ()
  end

let dump_eventlist evl =
  if !print_debug_flag then begin
    printf "{length evl=%d@." (List.length evl);
    let j = ref 0 in
    List.iter (fun ev ->
      print_ev_indexed  ev !j;
      j := !j + 1;
      ) evl;
    printf "}@.";
  end

let print_instr ic =
  let pos = currpos ic in
  List.iter print_event (Hashtbl.find_all event_table pos);
  let buf = Buffer.create 100 in
  let ppf = Format.formatter_of_buffer buf in
  let descr = ref "" in
  fprintf ppf "%8d  " (pos / 4);
  let op = inputu ic in
  if op >= Array.length Opnames.names_of_instructions || op < 0
  then (pp_print_string ppf "*** unknown opcode : "; pp_print_int ppf op)
  else pp_print_string ppf names_of_instructions.(op);
  begin try
    let info = List.assoc op op_info in
    let shape = fst info in
    descr := snd info;
    begin
    if shape <> Nothing then pp_print_string ppf " ";
    match shape with
    | Uint -> pp_print_int ppf (inputu ic)
    | Sint -> pp_print_int ppf (inputs ic)
    | Uint_Uint
       -> pp_print_int ppf (inputu ic); pp_print_string ppf ", "; pp_print_int ppf (inputu ic)
    | Disp -> let p = currpc ic in pp_print_int ppf (p + inputs ic)
    | Uint_Disp
       -> pp_print_int ppf (inputu ic); pp_print_string ppf ", ";
          let p = currpc ic in pp_print_int ppf (p + inputs ic)
    | Sint_Disp
       -> pp_print_int ppf (inputs ic); pp_print_string ppf ", ";
          let p = currpc ic in pp_print_int ppf (p + inputs ic)
    | Getglobal -> print_getglobal_name ppf ic
    | Getglobal_Uint
       -> print_getglobal_name ppf ic; pp_print_string ppf ", "; pp_print_int ppf (inputu ic)
    | Setglobal -> print_setglobal_name ppf ic
    | Primitive -> print_primitive ppf ic
    | Uint_Primitive
       -> pp_print_int ppf (inputu ic); pp_print_string ppf ", "; print_primitive ppf ic
    | Switch
       -> let n = inputu ic in
          let orig = currpc ic in
          for i = 0 to (n land 0xFFFF) - 1 do
            fprintf ppf "@.        int "; pp_print_int ppf i; pp_print_string ppf " -> ";
            pp_print_int ppf(orig + inputs ic);
          done;
          for i = 0 to (n lsr 16) - 1 do
            fprintf ppf "@.        tag "; pp_print_int ppf i; pp_print_string ppf " -> ";
            pp_print_int ppf(orig + inputs ic);
          done;
    | Closurerec
       -> let nfuncs = inputu ic in
          let nvars = inputu ic in
          let orig = currpc ic in
          pp_print_int ppf nvars;
          for _i = 0 to nfuncs - 1 do
            pp_print_string ppf ", ";
            pp_print_int ppf (orig + inputs ic);
          done;
    | Pubmet
       -> let tag = inputs ic in
          let _cache = inputu ic in
          pp_print_int ppf tag
    | Nothing -> ();
    end;
  with Not_found -> pp_print_string ppf " (unknown arguments)"
  end;
  fprintf ppf "@?";
  if not !keep_file then ()
  else
  let line = Buffer.contents buf in
  if !print_description_flag then begin
    let llen = String.length line in
    let tab_col = 45 in
    let pad_len = max 0 (tab_col - llen) in
    let padding = String.make pad_len ' ' in
    printf "%s %s ;%s@." line padding !descr
  end else
    printf "%s@." line
  

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
  if not (is_matching_module cu.cu_name) then ()
  else begin
    Load_path.init !extra_path;
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
      seek_in ic cu.cu_debug;
      let evl = (input_value ic : Instruct.debug_event list) in
      record_events 0 evl;
      let (dirs : string list) = input_value ic in
      List.iter add_expanded_dir dirs;
      let ok_to_print = ref true in
      let evl_len = List.length evl in
      if evl_len > 0  then begin
        ok_to_print := is_matching_module (List.hd evl).ev_module
      end;
      if !ok_to_print then begin
        if !print_debug_flag then begin
          printf "cu_debug=%u@." cu.cu_debug;
          let in_pos = pos_in ic in
          printf "in_pos=%u@." in_pos;
        end;
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
          let evl_len = List.length evl in
          if evl_len > 0 && is_matching_module (List.hd evl).ev_module then begin
            dump_eventlist evl
          end
        end
      end
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
  Load_path.init !extra_path;
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
      print_global std_formatter !globals.(i);
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
      let evl = (input_value ic : Instruct.debug_event list) in
      record_events orig evl;
      let (dirs : string list) = input_value ic in
      List.iter add_expanded_dir dirs;
      let ok_to_print = ref true in
      let evl_len = List.length evl in
      if evl_len > 0  then begin
        ok_to_print := is_matching_module (List.hd evl).ev_module
      end;
      if !ok_to_print then begin
        if !print_debug_flag then
          (printf "{orig=%d@." orig);
        if !print_dirs_flag then begin
          printf "@[<v 2>Debug directories=@,";
          List.iter (fun dir -> printf "%s@ " dir) dirs;
          printf "@]@.";
        end;
        if not !print_code_flag then begin
            dump_eventlist evl
        end;
        if !print_debug_flag then
          printf "}@."
      end
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
  let ocamlpath = Config.standard_library in
  printf "Ocaml lib=%s@." ocamlpath;
  the_filename := filename;
  the_realfile := Unix.realpath !the_filename;
  printf "the realfile = %s@." !the_realfile;
  find_workspace_roots ();

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

let add_path (adir: string) =
  extra_path := (adir :: (!extra_path));
  ()

let set_module_filter re_string =
  module_filter_string := re_string;
  module_filter_re := Some (Str.regexp re_string)

let arg_list = [
  "-approx", Arg.Set print_approx_flag,
    " Print module approximation information";
  "-no-approx", Arg.Clear print_approx_flag,
    " Do not print module approximation information";
  "-ce-filter", Arg.Set comp_env_filter_flag,
    " Only show environment in the computational environment,
      that is, what is available in the debugger";
  "-no-ce-filter", Arg.Clear comp_env_filter_flag,
    " Do no filter using the computational environment";
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
  "-describe", Arg.Set print_description_flag,
    " Print descriptions of opcode in opcode listing";
  "-no-describe", Arg.Clear print_description_flag,
    " Do not print descriptions of opcode in opcode listing";
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
  "-I", Arg.String add_path,
    "'-I s' adds 's' to the path to search for sources";
  "-imports", Arg.Set print_imports_flag,
    " Print imports";
  "-no-imports", Arg.Clear print_imports_flag,
    " Do not print imports";
  "-locations", Arg.Set print_locations_flag,
    " Print locations of debug events";
  "-no-locations", Arg.Clear print_locations_flag,
    " Do not print locations of debug events";
  "-mod-filter", Arg.String set_module_filter,
    "'-mod-filter re' will filter output to only output for modules matching re";
  "-primitives", Arg.Set print_primitives_flag,
    " Print primitives used table";
  "-no-primitives", Arg.Clear print_primitives_flag,
    " Do not print primitives used table";
  "-reloc", Arg.Set print_reloc_info_flag, " Print relocation information for the code";
  "-no-reloc", Arg.Clear print_reloc_info_flag, " Do not print relocation information for the code";
  "-source", Arg.Set print_source_flag, " Print source with code";
  "-no-source", Arg.Clear print_source_flag, " Do not print source with code";
  "-src-filter", Arg.Set_string desired_source_filename, 
    "'-src_filter src' only shows instructions for events related to src";
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
