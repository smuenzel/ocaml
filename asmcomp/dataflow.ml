(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cambium, INRIA Paris                  *)
(*                                                                        *)
(*   Copyright 2021 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

open Mach

module type DOMAIN = sig
  type t
  val bot: t
  val join: t -> t -> t
  val lessequal: t -> t -> bool
end

module Backward(D: DOMAIN) = struct

let analyze ?(exnhandler = fun x -> x) ?(exnescape = D.bot) ~transfer instr =

  let lbls =
    (Hashtbl.create 20 : (int, D.t) Hashtbl.t) in
  let get_lbl n =
    match Hashtbl.find_opt lbls n with None -> D.bot | Some b -> b
  and set_lbl n x =
    Hashtbl.replace lbls n x in

  let rec rev_instr acc i =
    match i.desc with
    | Ireturn | Iop (Itailcall_ind | Itailcall_imm _)
    | Iend -> i :: acc
    | _ -> rev_instr (i :: acc) i.next
  in

  let rec before end_ exn i =
    let rec loop rest bx =
      match rest with
      | [] -> bx
      | i :: rest ->
          match i.desc with
          | Iend ->
              loop rest (transfer i ~next:end_ ~exn)
          | Ireturn | Iop (Itailcall_ind | Itailcall_imm _) ->
              loop rest (transfer i ~next:D.bot ~exn:D.bot)
          | Iop _ ->
              loop rest (transfer i ~next:bx ~exn)
          | Iifthenelse(_, ifso, ifnot) ->
              let b1 = before bx exn ifso
              and b0 = before bx exn ifnot in
              loop rest (transfer i ~next:(D.join b1 b0) ~exn)
          | Iswitch(_, cases) ->
              let b1 =
                Array.fold_left
                  (fun accu case -> D.join accu (before bx exn case))
                  D.bot cases in
              loop rest (transfer i ~next:b1 ~exn)
          | Icatch(rc, handlers, body) ->
              begin match rc with
              | Cmm.Nonrecursive ->
                  List.iter
                    (fun (n, h) -> set_lbl n (before bx exn h))
                    handlers
              | Cmm.Recursive ->
                  let update changed (n, h) =
                    let b0 = get_lbl n in
                    let b1 = before bx exn h in
                    if D.lessequal b1 b0 then changed else (set_lbl n b1; true) in
                  while List.fold_left update false handlers do () done
              end;
              let b = before bx exn body in
              loop rest (transfer i ~next:b ~exn)
          | Iexit n ->
              loop rest (transfer i ~next:(get_lbl n) ~exn)
          | Itrywith(body, handler) ->
              let bh = exnhandler (before bx exn handler) in
              let bb = before bx bh body in
              loop rest (transfer i ~next:bb ~exn)
          | Iraise _ ->
              loop rest (transfer i ~next:D.bot ~exn)
    in
    loop (rev_instr [] i) end_
  in
  let b = before D.bot exnescape instr in
  (b, get_lbl)

end
