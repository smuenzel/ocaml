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

let rec apply_pass f expr =
  let result_base = f expr in
  match result_base with
  | Cconst_int _
  | Cconst_natint _
  | Cconst_float _
  | Cconst_symbol _
  | Cconst_pointer _
  | Cconst_natpointer _
  | Cblockheader _
  | Cvar _
    -> result_base
  | Clet (bv,e1,e2) ->
      let e1' = apply_pass f e1 in
      let e2' = apply_pass f e2 in
      if not (e1' == e1 && e2' == e2)
      then Clet (bv, e1', e2')
      else result_base
  | Cphantom_let (bv, pde, e1) ->
      let e1' = apply_pass f e1 in
      if not (e1' == e1)
      then Cphantom_let (bv, pde, e1')
      else result_base
  | Cassign (bv, e1) ->
      let e1' = apply_pass f e1 in
      if not (e1' == e1)
      then Cassign (bv, e1')
      else result_base
  | Ctuple el ->
      let el' = List.map (apply_pass f) el in
      Ctuple el'
  | Cop (op, el, dbg) ->
      let el' = List.map (apply_pass f) el in
      Cop (op, el', dbg)
  | Csequence (e1, e2) ->
      let e1' = apply_pass f e1 in
      let e2' = apply_pass f e2 in
      if not (e1' == e1 && e2' == e2)
      then Csequence (e1', e2')
      else result_base
  | Cifthenelse (e1, dbg1, e2, dbg2, e3, dbg3) ->
      let e1' = apply_pass f e1 in
      let e2' = apply_pass f e2 in
      let e3' = apply_pass f e3 in
      if not (e1' == e1 && e2' == e2 && e3 == e3')
      then Cifthenelse (e1',dbg1,e2',dbg2,e3',dbg3)
      else result_base
  | Cswitch (e1, iar, expar, dbg) ->
      let e1' = apply_pass f e1 in
      let expar' = Array.map (fun (e,dbg) -> apply_pass f e, dbg) expar in
      Cswitch (e1', iar, expar', dbg)
  | Ccatch (rf, handlers, e1) ->
      let e1' = apply_pass f e1 in
      let handlers' =
        List.map (fun (i,bvps, e, dbg) -> i,bvps,(apply_pass f e), dbg) handlers
      in
      Ccatch (rf, handlers', e1')
  | Cexit (i, exprs) ->
      let exprs' = List.map (apply_pass f) exprs in
      Cexit (i, exprs')
  | Ctrywith (e1,bvp, e2, dbg) ->
      let e1' = apply_pass f e1 in
      let e2' = apply_pass f e2 in
      if not (e1' == e1 && e2' == e2)
      then Ctrywith (e1', bvp, e2', dbg)
      else result_base

let rec equal_no_dbg e1 e2 =
  match e1, e2 with
  | Cconst_int (i1,_), Cconst_int (i2, _) ->
      i1 = i2
  | Cconst_natint (i1,_), Cconst_natint (i2,_) ->
      i1 = i2
  | Cconst_float (f1,_), Cconst_float (f2,_) ->
      f1 = f2
  | Cconst_symbol (s1,_), Cconst_symbol (s2,_) ->
      s1 = s2
  | Cconst_pointer (p1,_), Cconst_pointer (p2,_) ->
      p1 = p2
  | Cconst_natpointer (p1,_), Cconst_natpointer (p2,_) ->
      p1 = p2
  | Cblockheader (b1,_), Cblockheader (b2, _) ->
      b1 = b2
  | Cvar v1, Cvar v2 ->
      v1 = v2
  | Clet _, Clet _ ->
      (* TODO: extract shared things??? *)
      false
  | Cphantom_let _, _ | _, Cphantom_let _ ->
      false
  | Cassign (b1,e1), Cassign (b2,e2) ->
      (b1 = b2) && (equal_no_dbg e1 e2)
  | Ctuple e1s, Ctuple e2s ->
      begin try List.for_all2 equal_no_dbg e1s e2s with
      | Invalid_argument _ -> false
      end
  | Cop (op1, e1s, _), Cop (op2, e2s, _) ->
      let result =
        (op1 = op2)
        &&
        begin try List.for_all2 equal_no_dbg e1s e2s with
        | Invalid_argument _ -> false
        end
      in
      result
  | Csequence (s1e1, s1e2), Csequence (s2e1,s2e2) ->
      (equal_no_dbg s1e1 s2e1)
      &&
      (equal_no_dbg s1e2 s2e2)
  | Cifthenelse (s1e1, _, s1e2, _, s1e3, _)
  , Cifthenelse (s2e1, _, s2e2, _, s2e3, _) ->
      (equal_no_dbg s1e1 s2e1)
      &&
      (equal_no_dbg s1e2 s2e2)
      &&
      (equal_no_dbg s1e3 s2e3)
  | _, _ -> false

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
      apply_body1 body
        (fun body -> Cphantom_let(var, pde, body))
  | Clet(id, exp, body) ->
      apply_body1 body
        (fun body -> Clet(id, exp, body))
  | Csequence(e1, e2) ->
      apply_body1 e2
        (fun e2 -> Csequence(e1,e2))
  | Cifthenelse(cond, dbg_cond, e1, dbg_e1, e2, dbg_e2) ->
      apply_body2 e1 e2
        (fun e1 e2 -> Cifthenelse (cond, dbg_cond, e1, dbg_e1,e2, dbg_e2))
  | Cswitch(e, tbl, el, dbg') ->
      let sub_apply_tails
        , sub_apply_next_apply_funs
        = 
        Misc.Stdlib.Array.map_unzip
          (fun (e, dbg) ->
             let tl, na = apply_tails e in
             tl, (na, dbg)
          ) el
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
  | Ctrywith(e1, id, e2, dbg) when false ->
      (* Ctrywith is only safe when the tail cannot throw! 
         e.g. if the tails are:
         (app{typing/ctype.ml:875,6-37} "camlCtype__update_level_3216" env/7926
           level/7925 1a ty/7928 val)
         AND
         (app{typing/ctype.ml:878,6-36} "camlCtype__update_level_3216" env/7926
          level/7925 3a ty/7928 val)

         we could end up with nonsense like:
         (app{typing/ctype.ml:875,6-37;typing/ctype.ml:878,6-36}
            "camlCtype__update_level_3216" env/7926 level/7925
            (try 1a with exn/7935
              (if (== (load_mut val exn/7935) "camlCtype__Pmakeblock_22225")
                (let
                  (param/7942 (load_mut val (+a snap/7934 8))
                   sequence/7944
                     (app{typing/ctype.ml:877,6-20} "camlBtype__backtrack_3098"
                       (load_mut val snap/7934) param/7942 val))
                  3a)
                (raise_withtrace exn/7935)))
            ty/7928 val)
      *)
      apply_body2 e1 e2
        (fun e1 e2 -> Ctrywith(e1, id, e2, dbg))
  | Ccatch(rec_flag, handlers, body) ->
      let all_tails_body, next_apply_fun_body = apply_tails body in
      let sub_apply_tails
        , sub_apply_next_apply_funs
        =
        Misc.Stdlib.List.map_unzip
          (fun (n, ids, handler, dbg) ->
             let tl, na = apply_tails handler in
             tl, (n, ids, na, dbg)
          )
          handlers
      in
      let apply_fun newtail =
        let body, newtail = next_apply_fun_body newtail in
        let newtail = ref newtail in
        let handlers =
          List.map
            (fun (n, ids, af, dbg) ->
               let e, cs = af !newtail in
               newtail := cs;
               (n, ids, e, dbg)
            )
            sub_apply_next_apply_funs
        in
        Ccatch(rec_flag, handlers, body)
      , !newtail
      in
      let all_tails = all_tails_body @ (List.concat sub_apply_tails) in
      all_tails, apply_fun
  | Cop (Craise _, _, _) as cmm ->
      [ ]
    , fun cs -> cmm, cs
  | c ->
      [ c ]
    , function 
      | c :: cs -> c, cs
      | _ -> assert false
and apply_body1 body f =
  let all_tails, next_apply_fun = apply_tails body in
  let apply_fun newtail =
    let body, cs = next_apply_fun newtail in
    f body
  , cs
  in
  all_tails, apply_fun
and apply_body2 body1 body2 f =
  let all_tails_body1, next_apply_fun_body1 = apply_tails body1 in
  let all_tails_body2, next_apply_fun_body2 = apply_tails body2 in
  let apply_fun newtail =
    let body1, cs = next_apply_fun_body1 newtail in
    let body2, cs = next_apply_fun_body2 cs in
    f body1 body2
  , cs
  in
  let all_tails = List.append all_tails_body1 all_tails_body2 in
  all_tails, apply_fun

let apply_tails expr =
  let tails, mapper = apply_tails expr in
  let mapper elist =
    let e, remainder = mapper elist in
    assert (remainder = [] );
    e
  in
  tails, mapper
