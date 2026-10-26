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

  let current_unit = ref Misc.Stdlib.String.Map.empty

  let reset () =
    Misc.Stdlib.String.Tbl.clear registry;
    current_unit := Misc.Stdlib.String.Map.empty

  let add_from_current_unit name regs =
    Misc.Stdlib.String.Tbl.replace registry name regs;
    current_unit := Misc.Stdlib.String.Map.add name regs !current_unit

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

  let in_current_unit () =
    let elts = Misc.Stdlib.String.Map.bindings !current_unit in
    List.map
      (fun (name,regs) ->
         let regs = Array.to_list regs in
         let regs = List.filter_map
             (fun reg ->
                match reg.Reg.loc with
                | Reg.Unknown | Reg.Stack _ -> None
                | Reg.Reg r -> Some r
             ) regs
         in
         (name,Array.of_list regs)
      ) elts
end

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

let add_register_array acc instr_array =
  Array.fold_left
    (fun acc reg ->
       match reg.Reg.loc with
       | Reg i ->
           Reg.Set.add (Proc.phys_reg i) acc
       | Stack _ ->
           acc
       | Unknown ->
           Misc.fatal_error
             "Register_usage.all_registers_destroyed \
              must run after register allocation"
    )
    acc
    instr_array

let destroyed_transistive fname : Mach.instruction_desc -> Reg.t array = function
  | Iop (Icall_imm { func }) | Iop (Itailcall_imm { func }) when func = fname ->
      [||]
  | Iop (Itailcall_imm { func }) ->
      begin match Registry.destroyed_in_function func with
      | Some regs -> regs
      | None -> Proc.destroyed_at_oper (Iop (Icall_imm { func }))
      end
  | Iop Itailcall_ind ->
      Proc.destroyed_at_oper (Iop Icall_ind)
  | desc ->
      destroyed_at_oper desc

let all_registers_destroyed (fundecl : Mach.fundecl) =
  let set =
    Mach.instr_fold
      (fun acc instr ->
         let acc = add_register_array acc instr.res in
         add_register_array acc (destroyed_transistive fundecl.fun_name instr.desc)
      )
      destroyed_at_function_entry
      fundecl.fun_body
  in
  Array.of_list (Reg.Set.to_list set)

let fundecl fundecl =
  let destroyed = all_registers_destroyed fundecl in
  Registry.add_from_current_unit fundecl.Mach.fun_name destroyed;
  fundecl
