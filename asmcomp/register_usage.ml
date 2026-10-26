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

module Registry = struct
  type t = Reg.t array Misc.Stdlib.String.Tbl.t

  let (registry : t) = Misc.Stdlib.String.Tbl.create 17

  let reset () = Misc.Stdlib.String.Tbl.clear registry

  let add name regs =
    Misc.Stdlib.String.Tbl.replace registry name regs

  let add_from_cmx map =
    List.iter
      (fun (name,regs) ->
         let regs =
           Array.map
             Proc.phys_reg
             regs
         in
         add name regs
      ) map

  let destroyed_in_function name =
    Misc.Stdlib.String.Tbl.find_opt registry name
end

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

let destroyed_at_oper : Mach.instruction_desc -> Reg.t array = function
  | Iop (Icall_imm { func }) as desc ->
      begin match Registry.destroyed_in_function func with
      | Some regs -> regs
      | None ->
          Proc.destroyed_at_oper desc
      end
  | desc ->
      Proc.destroyed_at_oper desc

let all_registers_destroyed (fundecl : Mach.fundecl) =
  Mach.instr_fold
    (fun acc instr ->
       let acc = add_register_array acc instr.res in
       add_register_array acc (destroyed_at_oper instr.desc)
    )
    destroyed_at_function_entry
    fundecl.fun_body

