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

type machtype_component =
  | Val
  | Addr
  | Int
  | Float

type machtype = machtype_component array

let typ_void = ([||] : machtype_component array)
let typ_val = [|Val|]
let typ_addr = [|Addr|]
let typ_int = [|Int|]
let typ_float = [|Float|]

let size_component = function
  | Val | Addr -> Arch.size_addr
  | Int -> Arch.size_int
  | Float -> Arch.size_float

(** [machtype_component]s are partially ordered as follows:

      Addr     Float
       ^
       |
      Val
       ^
       |
      Int

  In particular, [Addr] must be above [Val], to ensure that if there is
  a join point between a code path yielding [Addr] and one yielding [Val]
  then the result is treated as a derived pointer into the heap (i.e. [Addr]).
  (Such a result may not be live across any call site or a fatal compiler
  error will result.)
*)

let lub_component comp1 comp2 =
  match comp1, comp2 with
  | Int, Int -> Int
  | Int, Val -> Val
  | Int, Addr -> Addr
  | Val, Int -> Val
  | Val, Val -> Val
  | Val, Addr -> Addr
  | Addr, Int -> Addr
  | Addr, Addr -> Addr
  | Addr, Val -> Addr
  | Float, Float -> Float
  | (Int | Addr | Val), Float
  | Float, (Int | Addr | Val) ->
    (* Float unboxing code must be sure to avoid this case. *)
    assert false

let ge_component comp1 comp2 =
  match comp1, comp2 with
  | Int, Int -> true
  | Int, Addr -> false
  | Int, Val -> false
  | Val, Int -> true
  | Val, Val -> true
  | Val, Addr -> false
  | Addr, Int -> true
  | Addr, Addr -> true
  | Addr, Val -> true
  | Float, Float -> true
  | (Int | Addr | Val), Float
  | Float, (Int | Addr | Val) ->
    assert false

let size_machtype mty =
  let size = ref 0 in
  for i = 0 to Array.length mty - 1 do
    size := !size + size_component mty.(i)
  done;
  !size

type integer_comparison = Lambda.integer_comparison =
  | Ceq | Cne | Clt | Cgt | Cle | Cge

let negate_integer_comparison = Lambda.negate_integer_comparison

let swap_integer_comparison = Lambda.swap_integer_comparison

(* With floats [not (x < y)] is not the same as [x >= y] due to NaNs,
   so we provide additional comparisons to represent the negations.*)
type float_comparison = Lambda.float_comparison =
  | CFeq | CFneq | CFlt | CFnlt | CFgt | CFngt | CFle | CFnle | CFge | CFnge

let negate_float_comparison = Lambda.negate_float_comparison

let swap_float_comparison = Lambda.swap_float_comparison
type label = int

let label_counter = ref 99

let new_label() = incr label_counter; !label_counter

type raise_kind =
  | Raise_withtrace
  | Raise_notrace

type rec_flag = Nonrecursive | Recursive

type phantom_defining_expr =
  | Cphantom_const_int of Targetint.t
  | Cphantom_const_symbol of string
  | Cphantom_var of Backend_var.t
  | Cphantom_offset_var of { var : Backend_var.t; offset_in_words : int; }
  | Cphantom_read_field of { var : Backend_var.t; field : int; }
  | Cphantom_read_symbol_field of { sym : string; field : int; }
  | Cphantom_block of { tag : int; fields : Backend_var.t list; }

type memory_chunk =
    Byte_unsigned
  | Byte_signed
  | Sixteen_unsigned
  | Sixteen_signed
  | Thirtytwo_unsigned
  | Thirtytwo_signed
  | Word_int
  | Word_val
  | Single
  | Double
  | Double_u

and operation =
    Capply of machtype
  | Cextcall of string * machtype * bool * label option
    (** If specified, the given label will be placed immediately after the
        call (at the same place as any frame descriptor would reference). *)
  | Cload of memory_chunk * Asttypes.mutable_flag
  | Calloc
  | Cstore of memory_chunk * Lambda.initialization_or_assignment
  | Caddi | Csubi | Cmuli | Cmulhi | Cdivi | Cmodi
  | Cand | Cor | Cxor | Clsl | Clsr | Casr
  | Ccmpi of integer_comparison
  | Caddv | Cadda
  | Ccmpa of integer_comparison
  | Cnegf | Cabsf
  | Caddf | Csubf | Cmulf | Cdivf
  | Cfloatofint | Cintoffloat
  | Ccmpf of float_comparison
  | Craise of raise_kind
  | Ccheckbound

type expression =
    Cconst_int of int * Debuginfo.t
  | Cconst_natint of nativeint * Debuginfo.t
  | Cconst_float of float * Debuginfo.t
  | Cconst_symbol of string * Debuginfo.t
  | Cconst_pointer of int * Debuginfo.t
  | Cconst_natpointer of nativeint * Debuginfo.t
  | Cblockheader of nativeint * Debuginfo.t
  | Cvar of Backend_var.t
  | Clet of Backend_var.With_provenance.t * expression * expression
  | Cphantom_let of Backend_var.With_provenance.t
      * phantom_defining_expr option * expression
  | Cassign of Backend_var.t * expression
  | Ctuple of expression list
  | Cop of operation * expression list * Debuginfo.t
  | Csequence of expression * expression
  | Cifthenelse of expression * Debuginfo.t * expression
      * Debuginfo.t * expression * Debuginfo.t
  | Cswitch of expression * int array * (expression * Debuginfo.t) array
      * Debuginfo.t
  | Ccatch of
      rec_flag
        * (int * (Backend_var.With_provenance.t * machtype) list
          * expression * Debuginfo.t) list
        * expression
  | Cexit of int * expression list
  | Ctrywith of expression * Backend_var.With_provenance.t * expression
      * Debuginfo.t

type codegen_option =
  | Reduce_code_size
  | No_CSE

type fundecl =
  { fun_name: string;
    fun_args: (Backend_var.With_provenance.t * machtype) list;
    fun_body: expression;
    fun_codegen_options : codegen_option list;
    fun_dbg : Debuginfo.t;
  }

type data_item =
    Cdefine_symbol of string
  | Cglobal_symbol of string
  | Cint8 of int
  | Cint16 of int
  | Cint32 of nativeint
  | Cint of nativeint
  | Csingle of float
  | Cdouble of float
  | Csymbol_address of string
  | Cstring of string
  | Cskip of int
  | Calign of int

type phrase =
    Cfunction of fundecl
  | Cdata of data_item list

let ccatch (i, ids, e1, e2, dbg) =
  Ccatch(Nonrecursive, [i, ids, e2, dbg], e1)

let reset () =
  label_counter := 99

let rec map_tail f = function
  | Cphantom_let(var, pde, body) ->
      Cphantom_let(var, pde, map_tail f body)
  | Clet(id, exp, body) ->
      Clet(id, exp, map_tail f body)
  | Cifthenelse(cond, dbg_cond, e1, dbg_e1, e2, dbg_e2) ->
      Cifthenelse
        (
          cond, dbg_cond,
          map_tail f e1, dbg_e1,
          map_tail f e2, dbg_e2
        )
  | Csequence(e1, e2) ->
      Csequence(e1, map_tail f e2)
  | Cswitch(e, tbl, el, dbg') ->
      Cswitch(e, tbl, Array.map (fun (e, dbg) -> map_tail f e, dbg) el, dbg')
  | Ccatch(rec_flag, handlers, body) ->
      let map_h (n, ids, handler, dbg) = (n, ids, map_tail f handler, dbg) in
      Ccatch(rec_flag, List.map map_h handlers, map_tail f body)
  | Ctrywith(e1, id, e2, dbg) ->
      Ctrywith(map_tail f e1, id, map_tail f e2, dbg)
  | Cop (Craise _, _, _) as cmm ->
      cmm
  | c ->
      f c

let rec fold_tails f init = function
  | Cphantom_let(_var, _pde, body) ->
      fold_tails f init body
  | Clet(_id, _exp, body) ->
      fold_tails f init body
  | Cifthenelse(_cond, _dbg_cond, e1, _dbg_e1, e2, _dbg_e2) ->
      let init = fold_tails f init e1 in
      fold_tails f init e2
  | Csequence(_e1, e2) ->
      fold_tails f init e2
  | Cswitch(_e, _tbl, el, _dbg') ->
      Array.fold_left (fun init (exp,_dbg) -> fold_tails f init exp) init el
  | Ccatch(_rec_flag, handlers, body) ->
      List.fold_left
        (fun init (_n, _ids, handler, _dbg) -> fold_tails f init handler)
        (fold_tails f init body)
        handlers
  | Ctrywith(e1, _id, e2, _dbg) ->
      let init = fold_tails f init e1 in
      fold_tails f init e2
  | Cop (Craise _, _, _) ->
      init
  | c ->
      f init c

let rec apply_tails = function
  | Cphantom_let(var, pde, body) ->
      let all_tails, next_apply_fun = apply_tails body in
      let apply_fun newtail =
        let body, cs = next_apply_fun newtail in
        Cphantom_let(var, pde, body)
      , cs
      in
      all_tails, apply_fun
  | Clet(id, exp, body) ->
      let all_tails, next_apply_fun = apply_tails body in
      let apply_fun newtail =
        let body, cs = next_apply_fun newtail in
        Clet(id, exp, body)
      , cs
      in
      all_tails, apply_fun
  | Csequence(e1, e2) ->
      let all_tails, next_apply_fun = apply_tails e2 in
      let apply_fun newtail =
        let e2, cs = next_apply_fun newtail in
        Csequence(e1, e2)
      , cs
      in
      all_tails, apply_fun
  | Cifthenelse(cond, dbg_cond, e1, dbg_e1, e2, dbg_e2) ->
      let all_tails_e1, next_apply_fun_e1 = apply_tails e1 in
      let all_tails_e2, next_apply_fun_e2 = apply_tails e2 in
      let apply_fun newtail =
        let e1, cs = next_apply_fun_e1 newtail in
        let e2, cs = next_apply_fun_e2 cs in
        Cifthenelse
          (
            cond, dbg_cond,
            e1, dbg_e1,
            e2, dbg_e2
          )
      , cs
      in
      let all_tails = List.append all_tails_e1 all_tails_e2 in
      all_tails, apply_fun
  | Cswitch(e, tbl, el, dbg') ->
      let sub_apply_tails
        , sub_apply_next_apply_funs = 
        let length = Array.length el in
        let tls = Array.make length [] in
        let nap = Array.make length ((fun _ -> assert false), Debuginfo.none) in
        Array.iteri
          (fun i (e, dbg) -> 
             let tl, na = apply_tails e in
             Array.unsafe_set tls i tl;
             Array.unsafe_set nap i (na, dbg);
          ) el;
        tls, nap
      in
      let apply_fun newtail =
        let newtail = ref newtail in
        let el =
          Array.map
            (fun (af, dbg) ->
               let e, cs = af !newtail in
               newtail := cs;
               e, dbg
            ) sub_apply_next_apply_funs
        in
        Cswitch(e, tbl, el, dbg')
      , !newtail
      in
      let all_tails = List.concat (Array.to_list sub_apply_tails) in
      all_tails, apply_fun
  | c ->
      [ c ]
    , function 
      | c :: cs -> c, cs
      | _ -> assert false
      (*
  | Ccatch(rec_flag, handlers, body) ->
      let map_h (n, ids, handler, dbg) = (n, ids, map_tail f handler, dbg) in
      Ccatch(rec_flag, List.map map_h handlers, map_tail f body)
  | Ctrywith(e1, id, e2, dbg) ->
      Ctrywith(map_tail f e1, id, map_tail f e2, dbg)
  | Cop (Craise _, _, _) as cmm ->
      cmm
  | c ->
      f c
         *)

let apply_tails expr =
  let tails, mapper = apply_tails expr in
  let mapper elist =
    let e, remainder = mapper elist in
    assert (remainder = [] );
    e
  in
  tails, mapper
