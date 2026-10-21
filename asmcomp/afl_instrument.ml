(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                 Stephen Dolan, University of Cambridge                 *)
(*                                                                        *)
(*   Copyright 2016 Stephen Dolan.                                        *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Insert instrumentation for afl-fuzz *)

open Lambda
open Cmm

open Cmm_helpers.Syntax


let afl_area_ptr dbg = Cconst_symbol ("caml_afl_area_ptr", dbg)
let afl_prev_loc dbg = Cconst_symbol ("caml_afl_prev_loc", dbg)
let afl_map_size = 1 lsl 16

let rec with_afl_logging b dbg =
  if !Clflags.afl_inst_ratio < 100 &&
    Random.int 100 >= !Clflags.afl_inst_ratio then instrument b else
  let instrumentation =
    (* The instrumentation that afl-fuzz requires is:

         cur_location = <COMPILE_TIME_RANDOM>;
         shared_mem[cur_location ^ prev_location]++;
         prev_location = cur_location >> 1;

       See http://lcamtuf.coredump.cx/afl/technical_details.txt or
       docs/technical_details.txt in afl-fuzz source for a full
       description of what's going on. *)
    let cur_location = Random.int afl_map_size in
    let op oper args = Cop (oper, args, dbg) in
    let opp oper args = Cpure_op (oper, args, dbg) in
    let= afl_area =
      "shared_mem",
      Cop (Cload ({memory_chunk=Word_int;
                   mutability=Asttypes.Mutable;
                   is_atomic=false}), [afl_area_ptr dbg], dbg)
    in
    let= prev_loc =
      "prev_location",
      Cop (Cload ({memory_chunk=Word_int;
                   mutability=Asttypes.Mutable;
                   is_atomic=false}), [afl_prev_loc dbg], dbg)
    in
    let= cur_pos =
      "pos",
      Cpure (opp Cxor [prev_loc; Cconst_int (cur_location, dbg)])
    in
    let= cur_value =
      "cur_value",
      Cop (Cload ({memory_chunk=Byte_unsigned;
                   mutability=Asttypes.Mutable;
                   is_atomic=false}),
           [opp Cadda [afl_area; cur_pos]], dbg)
    in
    Csequence(
      op (Cstore(Byte_unsigned, Assignment))
        [opp Cadda [afl_area; cur_pos];
         opp Cadda [cur_value;
                   Cconst_int (1, dbg)]],
      op (Cstore(Word_int, Assignment))
        [afl_prev_loc dbg; Cconst_int (cur_location lsr 1, dbg)]) in
  Csequence(instrumentation, instrument b)

and instrument = function
  (* these cases add logging, as they may be targets of conditional branches *)
  | Cifthenelse (cond, t_dbg, t, f_dbg, f, dbg) ->
     Cifthenelse (cond, t_dbg, with_afl_logging t t_dbg,
       f_dbg, with_afl_logging f f_dbg, dbg)
  | Ctrywith (e, ex, handler, dbg) ->
     Ctrywith (instrument e, ex, with_afl_logging handler dbg, dbg)
  | Cswitch (e, cases, handlers, dbg) ->
     let handlers =
       Array.map (fun (handler, handler_dbg) ->
           let handler = with_afl_logging handler handler_dbg in
           handler, handler_dbg)
         handlers
     in
     Cswitch (e, cases, handlers, dbg)

  (* these cases add no logging, but instrument subexpressions *)
  | Clet (v, e, body) -> Clet (v, instrument e, instrument body)
  | Clet_mut (v, k, e, body) ->
    Clet_mut (v, k, e, instrument body)
  | Cphantom_let (v, defining_expr, body) ->
    Cphantom_let (v, defining_expr, instrument body)
  | Cassign (v, e) -> Cassign (v, e)
  | Cop (op, es, dbg) -> Cop (op, es, dbg)
  | Csequence (e1, e2) -> Csequence (instrument e1, instrument e2)
  | Ccatch (isrec, cases, body) ->
     let cases =
       List.map (fun (nfail, ids, e, dbg) -> nfail, ids, instrument e, dbg)
         cases
     in
     Ccatch (isrec, cases, instrument body)
  | Cexit (ex, args) -> Cexit (ex, args)

  (* these are base cases and have no logging *)
  | Cpure _
  | Cvar_mut _ as c -> c

let instrument_function c dbg =
  with_afl_logging c dbg

let instrument_initialiser c dbg =
  (* Each instrumented module calls caml_setup_afl at
     initialisation, which is a no-op on the second and subsequent
     calls *)
  Csequence
   (Cop (Cextcall ("caml_setup_afl", typ_int, [], false),
         [Cconst_int (0, dbg ())],
         dbg ()),
    with_afl_logging c (dbg ()))
