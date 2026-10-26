(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                            Stefan Muenzel                              *)
(*                                                                        *)
(*   Copyright 2026 Stefan Muenzel.                                       *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

let add_register_array acc instr_array =
  Array.fold_left
    (fun acc reg ->
       match reg.Reg.loc with
       | Reg _ ->
           Reg.Set.add reg acc
       | Stack _ ->
           acc
       | Unknown ->
           Misc.fatal_error
             "Register_usage.all_registers_destroyed \
              must run after register allocation"
    )
    acc
    instr_array

let destroyed_at_function_entry =
  Reg.Set.of_list (Array.to_list Proc.destroyed_at_function_entry)

let all_registers_destroyed ~destroyed_in_function (fundecl : Mach.fundecl) =
  Mach.instr_fold
    (fun acc instr ->
       let acc = add_register_array acc instr.res in
       match instr.desc with
       | Iop (Icall_imm { func }) ->
           begin match destroyed_in_function func with
           | Some regs ->
               Reg.Set.union acc regs
           | None ->
               add_register_array acc (Proc.destroyed_at_oper instr.desc)
           end
       | _ ->
           add_register_array acc (Proc.destroyed_at_oper instr.desc)
    )
    destroyed_at_function_entry
    fundecl.fun_body
