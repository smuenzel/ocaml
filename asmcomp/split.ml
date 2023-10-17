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

(* Renaming of registers at reload points to split live ranges. *)

open Reg
open Mach

(* Substitutions are represented by register maps *)

type subst = Reg.t Reg.Map.t

let subst_reg r (sub : subst) =
  try
    Reg.Map.find r sub
  with Not_found ->
    r

let subst_regs rv sub =
  match sub with
    None -> rv
  | Some s ->
      let n = Array.length rv in
      let nv = Array.make n Reg.dummy in
      for i = 0 to n-1 do nv.(i) <- subst_reg rv.(i) s done;
      nv

type t = {
(* We maintain equivalence classes of registers using a standard
   union-find algorithm *)
  mutable equiv_classes : Reg.t Reg.Map.t;
  mutable exit_subst : (int * subst option ref) list
}

let empty () = {
  equiv_classes = Reg.Map.empty;
  exit_subst = []
}



let rec repres_reg t r =
  try
    repres_reg t (Reg.Map.find r t.equiv_classes)
  with Not_found ->
    r

let repres_regs t rv =
  let n = Array.length rv in
  for i = 0 to n-1 do rv.(i) <- repres_reg t rv.(i) done

(* Identify two registers.
   The second register is chosen as canonical representative. *)

let identify t r1 r2 =
  let repres1 = repres_reg t r1 in
  let repres2 = repres_reg t r2 in
  if repres1.stamp = repres2.stamp then () else begin
    t.equiv_classes <- Reg.Map.add repres1 repres2 t.equiv_classes
  end

(* Identify the image of a register by two substitutions.
   Be careful to use the original register as canonical representative
   in case it does not belong to the domain of one of the substitutions. *)

let identify_sub t sub1 sub2 reg =
  try
    let r1 = Reg.Map.find reg sub1 in
    try
      let r2 = Reg.Map.find reg sub2 in
      identify t r1 r2
    with Not_found ->
      identify t r1 reg
  with Not_found ->
    try
      let r2 = Reg.Map.find reg sub2 in
      identify t r2 reg
    with Not_found ->
      ()

(* Identify registers so that the two substitutions agree on the
   registers live before the given instruction. *)

let merge_substs t sub1 sub2 i =
  match (sub1, sub2) with
    (None, None) -> None
  | (Some _, None) -> sub1
  | (None, Some _) -> sub2
  | (Some s1, Some s2) ->
      Reg.Set.iter (identify_sub t s1 s2) (Reg.add_set_array i.live i.arg);
      sub1

(* Same, for N substitutions *)

let merge_subst_array t subv instr =
  let rec find_one_subst i =
    if i >= Array.length subv then None else begin
      match subv.(i) with
        None -> find_one_subst (i+1)
      | Some si as sub ->
          for j = i+1 to Array.length subv - 1 do
            match subv.(j) with
              None -> ()
            | Some sj ->
                Reg.Set.iter (identify_sub t si sj)
                             (Reg.add_set_array instr.live instr.arg)
          done;
          sub
    end in
  find_one_subst 0

(* First pass: rename registers at reload points *)

let find_exit_subst t k =
  try
    List.assoc k t.exit_subst with
  | Not_found -> Misc.fatal_error "Split.find_exit_subst"

let rec rename (t : t) i sub =
  match i.desc with
    Iend ->
      (i, sub)
  | Ireturn | Iop(Itailcall_ind) | Iop(Itailcall_imm _) ->
      (instr_cons_debug i.desc (subst_regs i.arg sub) [||] i.dbg i.next,
       None)
  | Iop Ireload when i.res.(0).loc = Unknown ->
      begin match sub with
        None -> rename t i.next sub
      | Some s ->
          let oldr = i.res.(0) in
          let newr = Reg.clone i.res.(0) in
          let (new_next, sub_next) =
            rename t i.next (Some(Reg.Map.add oldr newr s)) in
          (instr_cons i.desc i.arg [|newr|] new_next,
           sub_next)
      end
  | Iop _ ->
      let (new_next, sub_next) = rename t i.next sub in
      (instr_cons_debug i.desc (subst_regs i.arg sub) (subst_regs i.res sub)
                        i.dbg new_next,
       sub_next)
  | Iifthenelse(tst, ifso, ifnot) ->
      let (new_ifso, sub_ifso) = rename t ifso sub in
      let (new_ifnot, sub_ifnot) = rename t ifnot sub in
      let (new_next, sub_next) =
        rename t i.next (merge_substs t sub_ifso sub_ifnot i.next) in
      (instr_cons (Iifthenelse(tst, new_ifso, new_ifnot))
                  (subst_regs i.arg sub) [||] new_next,
       sub_next)
  | Iswitch(index, cases) ->
      let new_sub_cases = Array.map (fun c -> rename t c sub) cases in
      let sub_merge =
        merge_subst_array t (Array.map (fun (_n, s) -> s) new_sub_cases) i.next in
      let (new_next, sub_next) = rename t i.next sub_merge in
      (instr_cons (Iswitch(index, Array.map (fun (n, _s) -> n) new_sub_cases))
                  (subst_regs i.arg sub) [||] new_next,
       sub_next)
  | Icatch(rec_flag, handlers, body) ->
      let new_subst = List.map (fun (nfail, _) -> nfail, ref None)
          handlers in
      let previous_exit_subst = t.exit_subst in
      t.exit_subst <- new_subst @ t.exit_subst;
      let (new_body, sub_body) = rename t body sub in
      let res =
        List.map2 (fun (_, handler) (_, new_subst) -> rename t handler !new_subst)
          handlers new_subst in
      t.exit_subst <- previous_exit_subst;
      let merged_subst =
        List.fold_left (fun acc (_, sub_handler) ->
            merge_substs t acc sub_handler i.next)
          sub_body res in
      let (new_next, sub_next) = rename t i.next merged_subst in
      let new_handlers = List.map2 (fun (nfail, _) (handler, _) ->
          (nfail, handler)) handlers res in
      (instr_cons
         (Icatch(rec_flag, new_handlers, new_body)) [||] [||] new_next,
       sub_next)
  | Iexit nfail ->
      let r = find_exit_subst t nfail in
      r := merge_substs t !r sub i;
      (i, None)
  | Itrywith(body, handler) ->
      let (new_body, sub_body) = rename t body sub in
      let (new_handler, sub_handler) = rename t handler sub in
      let (new_next, sub_next) =
        rename t i.next (merge_substs t sub_body sub_handler i.next) in
      (instr_cons (Itrywith(new_body, new_handler)) [||] [||] new_next,
       sub_next)
  | Iraise k ->
      (instr_cons_debug (Iraise k) (subst_regs i.arg sub) [||] i.dbg i.next,
       None)

(* Second pass: replace registers by their final representatives *)

let set_repres t i =
  instr_iter (fun i -> repres_regs t i.arg; repres_regs t i.res) i

(* Entry point *)

let fundecl f =
  let t = empty () in

  let new_args = Array.copy f.fun_args in
  let (new_body, _sub_body) = rename t f.fun_body (Some Reg.Map.empty) in
  repres_regs t new_args;
  set_repres t new_body;
  { f with fun_args = new_args; fun_body = new_body }
