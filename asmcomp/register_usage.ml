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

module String_set = Misc.Stdlib.String.Set
module String_map = Misc.Stdlib.String.Map

module Registry = struct
  type t = Reg.t array Misc.Stdlib.String.Tbl.t

  let (registry : t) = Misc.Stdlib.String.Tbl.create 17

  let current_unit = ref String_map.empty

  let reset () =
    Misc.Stdlib.String.Tbl.clear registry;
    current_unit := Misc.Stdlib.String.Map.empty

  let reg_set_of_array array =
    Array.fold_left (fun acc reg -> Reg.Set.add reg acc) Reg.Set.empty array

  let array_of_reg_set set =
    let n = Reg.Set.cardinal set in
    let array = Array.make n Reg.dummy in
    let i = ref 0 in
    Reg.Set.iter (fun reg -> array.(!i) <- reg; incr i) set;
    array

  let destroyed_in_function_current_unit name =
    match String_map.find_opt name !current_unit with
    | None -> None
    | Some (regs, fns) ->
        let visited = ref String_set.empty in
        let rec loop name acc =
          if String_set.mem name !visited
          then acc
          else begin
            visited := String_set.add name !visited;
            match String_map.find_opt name !current_unit with
            | Some (regs, fns) ->
                let acc = Reg.Set.union regs acc in
                String_set.fold loop fns acc
            | None ->
                match Misc.Stdlib.String.Tbl.find_opt registry name with
                | Some regs -> Reg.Set.union (Reg.set_of_array regs) acc
                | None -> raise_notrace Exit
          end
        in
        try
          let result = String_set.fold loop fns regs in
          let result = array_of_reg_set result in
          Misc.Stdlib.String.Tbl.replace registry name result;
          Some result
        with
        | Exit -> None

  let destroyed_in_function name =
    match Misc.Stdlib.String.Tbl.find_opt registry name with
    | Some regs -> Some regs
    | None -> destroyed_in_function_current_unit name


  let add_from_current_unit name regs called_funs =
    current_unit := String_map.add name (reg_set_of_array regs, called_funs) !current_unit

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

  let in_current_unit () =
    let map = !current_unit in
    let result =
      String_map.fold
        (fun name _ acc ->
           match destroyed_in_function name with
           | Some regs ->
               let regs = Array.to_list regs in
               let regs = List.filter_map
                   (fun reg ->
                      match reg.Reg.loc with
                      | Reg.Unknown | Reg.Stack _ -> None
                      | Reg.Reg r -> Some r
                   ) regs
               in
               let regs = Array.of_list regs in
               (name, regs) :: acc
           | None -> acc
        )
        map
        []
    in
    List.rev result
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

let destroyed_transitive fname : Mach.instruction_desc -> _ = function
  | Iop (Icall_imm { func }) | Iop (Itailcall_imm { func }) when func = fname ->
      [||], []
  | Iop (Itailcall_imm { func }) ->
      begin match Registry.destroyed_in_function func with
      | Some regs -> regs, []
      | None -> [||], [ func ]
      end
  | Iop Itailcall_ind ->
      Proc.destroyed_at_oper (Iop Icall_ind), []
  | Iop (Icall_imm { func }) ->
      begin match Registry.destroyed_in_function func with
      | Some regs -> regs, []
      | None -> [||], [ func ]
      end
  | desc ->
      destroyed_at_oper desc, []

let all_registers_destroyed (fundecl : Mach.fundecl) =
  let set, called_funs =
    Mach.instr_fold
      (fun (acc, cacc) instr ->
         let acc = add_register_array acc instr.res in
         let destroyed, called_funs = destroyed_transitive fundecl.fun_name instr.desc in
         add_register_array acc destroyed, String_set.union (String_set.of_list called_funs) cacc
      )
      (destroyed_at_function_entry, String_set.empty)
      fundecl.fun_body
  in
  Array.of_list (Reg.Set.to_list set), called_funs

let fundecl fundecl =
  let destroyed, called_funs = all_registers_destroyed fundecl in
  Registry.add_from_current_unit fundecl.Mach.fun_name destroyed called_funs;
  fundecl

let max_register_pressure op =
  let default = Proc.max_register_pressure op in
  match op with
  | Mach.Icall_imm { func }->
      begin match Registry.destroyed_in_function func with
      | Some regs ->
          let ar = Array.copy default in
          Array.iter
            (fun reg ->
               let class_ = Proc.register_class reg in
               ar.(class_) <- ar.(class_) - 1
            )
            regs;
          ar
      | None ->
          Array.map (fun _ -> 0) default
      end
  | _ ->
      default

let safe_register_pressure op =
  match op with
  | Mach.Icall_imm _ -> 0
  | _ -> Proc.safe_register_pressure op
