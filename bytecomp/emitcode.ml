(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Generation of bytecode + relocation information *)

open Asttypes
open Config
open Misc
open Lambda
open Instruct
open Opcodes
open Cmo_format
module String = Misc.Stdlib.String

type error = Not_compatible_32 of (string * string)
exception Error of error

type label_definition =
    Label_defined of int
  | Label_undefined of (int * int) list



type t =
  { mutable out_buffer : (char, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t;
    mutable out_position : int;
    mutable reloc_info : (reloc_info * int) list;
    mutable events : debug_event list;
    mutable debug_dirs : String.Set.t;
    mutable label_table : label_definition array;
    mutable hints : (int * optimization_hint) list;
  }

(* marshal and possibly check 32bit compat *)
let marshal_to_channel_with_possibly_32bit_compat ~filename ~kind outchan obj =
  try
    Marshal.to_channel outchan obj
      (if !Clflags.bytecode_compatible_32
       then [Marshal.Compat_32] else [])
  with Failure _ ->
    raise (Error (Not_compatible_32 (filename, kind)))


let report_error ppf (file, kind) =
  Format_doc.fprintf ppf "Generated %s %S cannot be used on a 32-bit platform"
                     kind file
let () =
  Location.register_error_of_exn
    (function
      | Error (Not_compatible_32 info) ->
          Some (Location.error_of_printer_file report_error info)
      | _ ->
          None
    )

(* Buffering of bytecode *)
let create_bigarray = Bigarray.Array1.create Bigarray.Char Bigarray.c_layout

let copy_bigarray src dst size =
  Bigarray.Array1.(blit (sub src 0 size) (sub dst 0 size))


let extend_buffer t needed =
  let size = Bigarray.Array1.dim t.out_buffer in
  let new_size = ref(max size 16) (* we need new_size > 0 *) in
  while needed >= !new_size do new_size := 2 * !new_size done;
  let new_buffer = create_bigarray !new_size in
  copy_bigarray t.out_buffer new_buffer size;
  t.out_buffer <- new_buffer

let out_word t b1 b2 b3 b4 =
  let p = t.out_position in
  let open Bigarray.Array1 in
  if p+3 >= dim t.out_buffer then extend_buffer t (p+3);
  set t.out_buffer p (Char.unsafe_chr b1);
  set t.out_buffer (p+1) (Char.unsafe_chr b2);
  set t.out_buffer (p+2) (Char.unsafe_chr b3);
  set t.out_buffer (p+3) (Char.unsafe_chr b4);
  t.out_position <- p + 4

let out t opcode =
  out_word t opcode 0 0 0


exception AsInt

let const_as_int = function
  | Const_int i -> i
  | Const_char c -> Char.code c
  | _ -> raise AsInt

let is_immed i = immed_min <= i && i <= immed_max
let is_immed_const k =
  try
    is_immed (const_as_int k)
  with
  | AsInt -> false


let out_int t n =
  out_word t n (n asr 8) (n asr 16) (n asr 24)

let out_const t c =
  try
    out_int t (const_as_int c)
  with
  | AsInt -> Misc.fatal_error "Emitcode.const_as_int"


(* Handling of local labels and backpatching *)

let extend_label_table t needed =
  let size = Array.length t.label_table in
  let new_size = ref(max size 16) (* we need new_size > 0 *) in
  while needed >= !new_size do new_size := 2 * !new_size done;
  let new_table = Array.make !new_size (Label_undefined []) in
  Array.blit t.label_table 0 new_table 0 (Array.length t.label_table);
  t.label_table <- new_table

let backpatch t (pos, orig) =
  let displ = (t.out_position - orig) asr 2 in
  let open Bigarray.Array1 in
  set t.out_buffer pos (Char.unsafe_chr displ);
  set t.out_buffer (pos+1) (Char.unsafe_chr (displ asr 8));
  set t.out_buffer (pos+2) (Char.unsafe_chr (displ asr 16));
  set t.out_buffer (pos+3) (Char.unsafe_chr (displ asr 24))

let define_label t lbl =
  if lbl >= Array.length t.label_table then extend_label_table t lbl;
  match (t.label_table).(lbl) with
    Label_defined _ ->
      fatal_error "Emitcode.define_label"
  | Label_undefined patchlist ->
      List.iter (backpatch t) patchlist;
      (t.label_table).(lbl) <- Label_defined t.out_position

let out_label_with_orig t orig lbl =
  if lbl >= Array.length t.label_table then extend_label_table t lbl;
  match (t.label_table).(lbl) with
    Label_defined def ->
      out_int t ((def - orig) asr 2)
  | Label_undefined patchlist ->
      (t.label_table).(lbl) <-
         Label_undefined((t.out_position, orig) :: patchlist);
      out_int t 0

let out_label t l = out_label_with_orig t t.out_position l

(* Relocation information *)

let enter t info =
  t.reloc_info <- (info, t.out_position) :: t.reloc_info

let slot_for_literal t sc =
  enter t (Reloc_literal (Symtable.transl_const sc));
  out_int t 0
and slot_for_getglobal t id =
  let name = Ident.name id in
  let reloc_info =
    if Ident.is_predef id then (Reloc_getpredef (Predef_exn name))
    else if Ident.global id then (Reloc_getcompunit (Compunit name))
    else assert false
  in
  enter t reloc_info;
  out_int t 0
and slot_for_setglobal t id =
  let name = Ident.name id in
  let reloc_info =
    if Ident.persistent id then (Reloc_setcompunit (Compunit name))
    else assert false
  in
  enter t reloc_info;
  out_int t 0
and slot_for_c_prim t name =
  enter t (Reloc_primitive name);
  out_int t 0

(* Debugging events *)

let record_event t ev =
  let path = ev.ev_loc.Location.loc_start.Lexing.pos_fname in
  let abspath = Location.absolute_path path in
  t.debug_dirs <- String.Set.add (Filename.dirname abspath) t.debug_dirs;
  if Filename.is_relative path then begin
    let cwd = Location.rewrite_absolute_path (Sys.getcwd ()) in
    t.debug_dirs <- String.Set.add cwd t.debug_dirs;
  end;
  ev.ev_pos <- t.out_position;
  t.events <- ev :: t.events

let record_hint t hint = t.hints <- (t.out_position, hint) :: t.hints

let record_immediate_hint t (ptr : Lambda.immediate_or_pointer) =
  match ptr with
  | Immediate -> record_hint t Hint_immediate
  | Pointer -> ()

(* Initialization *)

let init () =
  { out_buffer = create_bigarray 1024;
    label_table = Array.make 16 (Label_undefined []);
    reloc_info = [];
    out_position = 0;
    debug_dirs = String.Set.empty;
    events = [];
    hints = [];
  }

(* Emission of one instruction *)

let emit_comp t = function
| Ceq -> out t opEQ    | Cne -> out t opNEQ
| Clt -> out t opLTINT | Cle -> out t opLEINT
| Cgt -> out t opGTINT | Cge -> out t opGEINT

and emit_branch_comp t = function
| Ceq -> out t opBEQ    | Cne -> out t opBNEQ
| Clt -> out t opBLTINT | Cle -> out t opBLEINT
| Cgt -> out t opBGTINT | Cge -> out t opBGEINT

let integer_comparison_of_physical : physical_comparison -> integer_comparison =
  function CPeq -> Ceq | CPneq -> Cne

let emit_instr t = function
    Klabel lbl -> define_label t lbl
  | Kacc n ->
      if n < 8 then out t (opACC0 + n) else (out t opACC; out_int t n)
  | Kenvacc n ->
      if n >= 1 && n <= 4
      then out t (opENVACC1 + n - 1)
      else (out t opENVACC; out_int t n)
  | Kpush ->
      out t opPUSH
  | Kpop n ->
      out t opPOP; out_int t n
  | Kassign n ->
      out t opASSIGN; out_int t n
  | Kpush_retaddr lbl -> out t opPUSH_RETADDR; out_label t lbl
  | Kapply n ->
      if n < 4 then out t (opAPPLY1 + n - 1) else (out t opAPPLY; out_int t n)
  | Kappterm(n, sz) ->
      if n < 4 then (out t (opAPPTERM1 + n - 1); out_int t sz)
               else (out t opAPPTERM; out_int t n; out_int t sz)
  | Kreturn n -> out t opRETURN; out_int t n
  | Krestart -> out t opRESTART
  | Kgrab n -> out t opGRAB; out_int t n
  | Kclosure(lbl, n, hint) ->
      record_hint t (Hint_closures [hint]);
      out t opCLOSURE; out_int t n; out_label t lbl
  | Kclosurerec(lbl_hints, n) ->
      record_hint t (Hint_closures (List.map snd lbl_hints));
      out t opCLOSUREREC; out_int t (List.length lbl_hints); out_int t n;
      let org = t.out_position in
      List.iter (fun (lbl, _) -> out_label_with_orig t org lbl) lbl_hints
  | Koffsetclosure ofs ->
      if ofs = -3 || ofs = 0 || ofs = 3
      then out t (opOFFSETCLOSURE0 + ofs / 3)
      else (out t opOFFSETCLOSURE; out_int t ofs)
  | Kgetglobal q -> out t opGETGLOBAL; slot_for_getglobal t q
  | Ksetglobal q -> out t opSETGLOBAL; slot_for_setglobal t q
  | Kconst sc ->
      begin match sc with
        Const_int i when is_immed i ->
          if i >= 0 && i <= 3
          then out t (opCONST0 + i)
          else (out t opCONSTINT; out_int t i)
      | Const_char c ->
          out t opCONSTINT; out_int t (Char.code c)
      | Const_block(t', []) ->
          if t' = 0 then out t opATOM0 else (out t opATOM; out_int t t')
      | _ ->
          out t opGETGLOBAL; slot_for_literal t sc
      end
  | Kmakeblock(n, t', mut) ->
      (match mut with
       | Immutable -> record_hint t Hint_immutable_block
       | Mutable -> ());
      if n = 0 then
        if t' = 0 then out t opATOM0 else (out t opATOM; out_int t t')
      else if n < 4 then (out t (opMAKEBLOCK1 + n - 1); out_int t t')
      else (out t opMAKEBLOCK; out_int t n; out_int t t')
  | Kgetfield (n, ptr) ->
      record_immediate_hint t ptr;
      if n < 4 then out t (opGETFIELD0 + n) else (out t opGETFIELD; out_int t n)
  | Ksetfield n ->
      if n < 4 then out t (opSETFIELD0 + n) else (out t opSETFIELD; out_int t n)
  | Kmakefloatblock(n, mut) ->
      (match mut with
       | Immutable -> record_hint t Hint_immutable_block
       | Mutable -> ());
      if n = 0 then out t opATOM0 else (out t opMAKEFLOATBLOCK; out_int t n)
  | Kgetfloatfield n -> out t opGETFLOATFIELD; out_int t n
  | Ksetfloatfield n -> out t opSETFLOATFIELD; out_int t n
  | Kvectlength kind ->
      record_hint t (Hint_arraylength kind);
      out t opVECTLENGTH
  | Kgetvectitem ptr ->
      record_immediate_hint t ptr;
      out t opGETVECTITEM
  | Ksetvectitem -> out t opSETVECTITEM
  | Kgetstringchar -> out t opGETSTRINGCHAR
  | Kgetbyteschar -> out t opGETBYTESCHAR
  | Ksetbyteschar -> out t opSETBYTESCHAR
  | Kbranch lbl -> out t opBRANCH; out_label t lbl
  | Kbranchif lbl -> out t opBRANCHIF; out_label t lbl
  | Kbranchifnot lbl -> out t opBRANCHIFNOT; out_label t lbl
  | Kstrictbranchif lbl -> out t opBRANCHIF; out_label t lbl
  | Kstrictbranchifnot lbl -> out t opBRANCHIFNOT; out_label t lbl
  | Kswitch(tbl_const, tbl_block) ->
      out t opSWITCH;
      out_int t (Array.length tbl_const + (Array.length tbl_block lsl 16));
      let org = t.out_position in
      Array.iter (out_label_with_orig t org) tbl_const;
      Array.iter (out_label_with_orig t org) tbl_block
  | Kboolnot -> out t opBOOLNOT
  | Kpushtrap lbl -> out t opPUSHTRAP; out_label t lbl
  | Kpoptrap -> out t opPOPTRAP
  | Kraise Raise_regular -> out t opRAISE
  | Kraise Raise_reraise -> out t opRERAISE
  | Kraise Raise_notrace -> out t opRAISE_NOTRACE
  | Kcheck_signals -> out t opCHECK_SIGNALS
  | Kccall(name, n, hint) ->
      (match hint with Some h -> record_hint t (Hint_ccall h) | None -> ());
      if n <= 5
      then (out t (opC_CALL1 + n - 1); slot_for_c_prim t name)
      else (out t opC_CALLN; out_int t n; slot_for_c_prim t name)
  | Knegint -> out t opNEGINT  | Kaddint -> out t opADDINT
  | Ksubint -> out t opSUBINT  | Kmulint -> out t opMULINT
  | Kdivint -> out t opDIVINT  | Kmodint -> out t opMODINT
  | Kandint -> out t opANDINT  | Korint -> out t opORINT
  | Kxorint -> out t opXORINT  | Klslint -> out t opLSLINT
  | Klsrint -> out t opLSRINT  | Kasrint -> out t opASRINT
  | Kintcomp c ->
      (match c with
       | Ceq | Cne -> record_hint t Hint_int_equality_test
       | Clt | Cle | Cgt | Cge -> ());
      emit_comp t c
  | Kphyscomp c ->
      emit_comp t (integer_comparison_of_physical c)
  | Koffsetint n -> out t opOFFSETINT; out_int t n
  | Koffsetref n -> out t opOFFSETREF; out_int t n
  | Kisint variant_only ->
      if variant_only then record_hint t Hint_variant;
      out t opISINT
  | Kisout -> out t opULTINT
  | Kgetmethod -> out t opGETMETHOD
  | Kgetpubmet tag -> out t opGETPUBMET; out_int t tag; out_int t 0
  | Kgetdynmet -> out t opGETDYNMET
  | Kevent ev -> record_event t ev
  | Kperform -> out t opPERFORM
  | Kresume -> out t opRESUME
  | Kresumeterm n -> out t opRESUMETERM; out_int t n
  | Kreperformterm n -> out t opREPERFORMTERM; out_int t n
  | Kstop -> out t opSTOP

(* Emission of a list of instructions. Include some peephole optimization. *)

let remerge_events ev1 = function
  | Kevent ev2 :: c ->
    Kevent (Bytegen.merge_events ev1 ev2) :: c
  | c -> Kevent ev1 :: c

let rec emit t = function
    [] -> ()
  (* Peephole optimizations *)
(* optimization of integer tests *)
  | Kpush::Kconst k::Kintcomp c::Kbranchif lbl::rem
      when is_immed_const k ->
        emit_branch_comp t c ;
        out_const t k ;
        out_label t lbl ;
        emit t rem
  | Kpush::Kconst k::Kintcomp c::Kbranchifnot lbl::rem
      when is_immed_const k ->
        emit_branch_comp t (negate_integer_comparison c) ;
        out_const t k ;
        out_label t lbl ;
        emit t rem
  | Kpush::Kconst k::Kphyscomp c::Kbranchif lbl::rem
      when is_immed_const k ->
        emit_branch_comp t (integer_comparison_of_physical c) ;
        out_const t k ;
        out_label t lbl ;
        emit t rem
  | Kpush::Kconst k::Kphyscomp c::Kbranchifnot lbl::rem
      when is_immed_const k ->
        emit_branch_comp t
          (negate_integer_comparison (integer_comparison_of_physical c)) ;
        out_const t k ;
        out_label t lbl ;
        emit t rem
(* same for range tests *)
  | Kpush::Kconst k::Kisout::Kbranchif lbl::rem
      when is_immed_const k ->
        out t opBULTINT ;
        out_const t k ;
        out_label t lbl ;
        emit t rem
  | Kpush::Kconst k::Kisout::Kbranchifnot lbl::rem
      when is_immed_const k ->
        out t opBUGEINT ;
        out_const t k ;
        out_label t lbl ;
        emit t rem
(* Some special case of push ; i ; ret generated by the match compiler *)
  | Kpush :: Kacc 0 :: Kreturn m :: c ->
      emit t (Kreturn (m-1) :: c)
(* General push then access scheme *)
  | Kpush :: Kacc n :: c ->
      if n < 8 then out t (opPUSHACC0 + n) else (out t opPUSHACC; out_int t n);
      emit t c
  | Kpush :: Kenvacc n :: c ->
      if n >= 1 && n <= 4
      then out t (opPUSHENVACC1 + n - 1)
      else (out t opPUSHENVACC; out_int t n);
      emit t c
  | Kpush :: Koffsetclosure ofs :: c ->
      if ofs = -3 || ofs = 0 || ofs = 3
      then out t (opPUSHOFFSETCLOSURE0 + ofs / 3)
      else (out t opPUSHOFFSETCLOSURE; out_int t ofs);
      emit t c
  | Kpush :: Kgetglobal id :: Kgetfield (n, ptr) :: c ->
      record_immediate_hint t ptr;
      out t opPUSHGETGLOBALFIELD; slot_for_getglobal t id; out_int t n; emit t c
  | Kpush :: Kgetglobal id :: c ->
      out t opPUSHGETGLOBAL; slot_for_getglobal t id; emit t c
  | Kpush :: Kconst sc :: c ->
      begin match sc with
        Const_int i when is_immed i ->
          if i >= 0 && i <= 3
          then out t (opPUSHCONST0 + i)
          else (out t opPUSHCONSTINT; out_int t i)
      | Const_char c ->
          out t opPUSHCONSTINT; out_int t (Char.code c)
      | Const_block(t', []) ->
          if t' = 0 then out t opPUSHATOM0 else (out t opPUSHATOM; out_int t t')
      | _ ->
          out t opPUSHGETGLOBAL; slot_for_literal t sc
      end;
      emit t c
  | Kpush :: (Kevent ({ev_kind = Event_before} as ev)) ::
    (Kgetglobal _ as instr1) :: (Kgetfield _ as instr2) :: c ->
      emit t (Kpush :: instr1 :: instr2 :: remerge_events ev c)
  | Kpush :: (Kevent ({ev_kind = Event_before} as ev)) ::
    (Kacc _ | Kenvacc _ | Koffsetclosure _ | Kgetglobal _ | Kconst _ as instr)::
    c ->
      emit t (Kpush :: instr :: remerge_events ev c)
  | Kgetglobal id :: Kgetfield (n, ptr) :: c ->
      record_immediate_hint t ptr;
      out t opGETGLOBALFIELD; slot_for_getglobal t id; out_int t n; emit t c
  (* Default case *)
  | instr :: c ->
      emit_instr t instr; emit t c

(* Emission to a file *)

let to_file outchan artifact_info ~required_globals code =
  let t = init () in
  output_string outchan cmo_magic_number;
  let pos_depl = pos_out outchan in
  output_binary_int outchan 0;
  let pos_code = pos_out outchan in
  emit t code;
  Out_channel.output_bigarray outchan t.out_buffer 0 t.out_position;
  let (pos_debug, size_debug) =
    if !Clflags.debug then begin
      let filename = Unit_info.Artifact.filename artifact_info in
      t.debug_dirs <- String.Set.add
          (Filename.dirname (Location.absolute_path filename))
        t.debug_dirs;
      let p = pos_out outchan in
      Compression.output_value outchan t.events;
      Compression.output_value outchan (String.Set.elements t.debug_dirs);
      (p, pos_out outchan - p)
    end else
      (0, 0) in
  let (pos_hint, size_hint) =
    let p = pos_out outchan in
    Compression.output_value outchan t.hints;
    (p, pos_out outchan - p)
  in
  let compunit =
    { cu_name = Cmo_format.Compunit (Unit_info.Artifact.modname artifact_info);
      cu_pos = pos_code;
      cu_codesize = t.out_position;
      cu_reloc = List.rev t.reloc_info;
      cu_imports = Env.imports();
      cu_primitives = List.map Primitive.byte_name
                               !Translmod.primitive_declarations;
      cu_required_compunits = List.map (fun id -> Compunit (Ident.name id))
        (Ident.Set.elements required_globals);
      cu_force_link = !Clflags.link_everything;
      cu_debug = pos_debug;
      cu_debugsize = size_debug;
      cu_hint = pos_hint;
      cu_hintsize = size_hint } in
  let pos_compunit = pos_out outchan in
  let () =
    (* Remove any cached abbreviation expansion before marshaling.
       See doc-comment for [Types.abbrev_memo] *)
    Btype.cleanup_abbrev_memo ();
    marshal_to_channel_with_possibly_32bit_compat
      ~filename:(Unit_info.Artifact.filename artifact_info)
      ~kind:"bytecode unit"
      outchan compunit
  in
  seek_out outchan pos_depl;
  output_binary_int outchan pos_compunit

(* Emission to a memory block *)

let to_memory instrs =
  let t = init() in
  emit t instrs;
  let code = create_bigarray t.out_position in
  copy_bigarray t.out_buffer code t.out_position;
  let reloc = List.rev t.reloc_info in
  let events = t.events in
  (code, reloc, events)

(* Emission to a file for a packed library *)

let to_packed_file outchan code =
  let t = init () in
  emit t code;
  Out_channel.output_bigarray outchan t.out_buffer 0 t.out_position;
  let reloc = List.rev t.reloc_info in
  let events = t.events in
  let debug_dirs = t.debug_dirs in
  let size = t.out_position in
  (size, reloc, events, debug_dirs, t.hints)
