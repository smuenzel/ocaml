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

module Physical_register_mask = struct
  (* Register [i] of class [c] is bit
     [class_shift c + i - Proc.first_available_register.(c)].
     Only allocatable registers are represented: the others never hold
     values across instructions, so callers don't care whether they are
     preserved. *)
  type t = int

  let empty = 0

  (* Lazy, since [Proc.init] can change [Proc.num_available_registers].
     Element [Proc.num_register_classes] is the total number of bits. *)
  let class_shifts =
    lazy begin
      let shifts = Array.make (Proc.num_register_classes + 1) 0 in
      for c = 0 to Proc.num_register_classes - 1 do
        shifts.(c + 1) <- shifts.(c) + Proc.num_available_registers.(c)
      done;
      assert (shifts.(Proc.num_register_classes) < Sys.int_size);
      shifts
    end

  let class_shift class_ = (Lazy.force class_shifts).(class_)

  let all () = (1 lsl class_shift Proc.num_register_classes) - 1

  let add_reg t (reg : Reg.t) =
    match reg.loc with
    | Reg i ->
        let class_ = Proc.register_class reg in
        let n = i - Proc.first_available_register.(class_) in
        if n < Proc.num_available_registers.(class_)
        then t lor (1 lsl (class_shift class_ + n))
        else t
    | Stack _ ->
        t
    | Unknown ->
        Misc.fatal_error
          "Register_usage.all_registers_destroyed \
           must run after register allocation"

  let add_array t regs = Array.fold_left add_reg t regs

  let of_array regs = add_array empty regs

  let count_in_class t class_ =
    let shift = class_shift class_ in
    let count = ref 0 in
    for n = 0 to Proc.num_available_registers.(class_) - 1 do
      if t land (1 lsl (shift + n)) <> 0 then incr count
    done;
    !count

  let arrays = Numbers.Int.Tbl.create 17

  let to_array t =
    match Numbers.Int.Tbl.find_opt arrays t with
    | Some regs -> regs
    | None ->
        let regs = ref [] in
        for class_ = Proc.num_register_classes - 1 downto 0 do
          let shift = class_shift class_ in
          let first = Proc.first_available_register.(class_) in
          for n = Proc.num_available_registers.(class_) - 1 downto 0 do
            if t land (1 lsl (shift + n)) <> 0 then
              regs := Proc.phys_reg (first + n) :: !regs
          done
        done;
        let regs = Array.of_list !regs in
        Numbers.Int.Tbl.add arrays t regs;
        regs
end

module Registry = struct
  type t = Physical_register_mask.t Misc.Stdlib.String.Tbl.t

  let (registry : t) = Misc.Stdlib.String.Tbl.create 17

  let current_unit = ref String_map.empty

  (* Functions of the current unit that reach a function without register
     usage information. Adding a function can complete them. *)
  let incomplete = Misc.Stdlib.String.Tbl.create 17

  let reset () =
    Misc.Stdlib.String.Tbl.clear registry;
    Misc.Stdlib.String.Tbl.clear incomplete;
    current_unit := Misc.Stdlib.String.Map.empty

  let destroyed_in_function_current_unit name =
    if not (String_map.mem name !current_unit)
    || Misc.Stdlib.String.Tbl.mem incomplete name
    then None
    else begin
      let visited = ref String_set.empty in
      let rec loop name acc =
        if String_set.mem name !visited
        then acc
        else begin
          visited := String_set.add name !visited;
          match String_map.find_opt name !current_unit with
          | Some (mask, fns) ->
              String_set.fold loop fns (acc lor mask)
          | None ->
              match Misc.Stdlib.String.Tbl.find_opt registry name with
              | Some mask -> acc lor mask
              | None -> raise_notrace Exit
        end
      in
      match loop name Physical_register_mask.empty with
      | result ->
          Misc.Stdlib.String.Tbl.replace registry name result;
          Some result
      | exception Exit ->
          Misc.Stdlib.String.Tbl.replace incomplete name ();
          None
    end

  let destroyed_in_function name =
    match Misc.Stdlib.String.Tbl.find_opt registry name with
    | Some mask -> Some mask
    | None -> destroyed_in_function_current_unit name

  let add_from_current_unit name mask called_funs =
    Misc.Stdlib.String.Tbl.clear incomplete;
    current_unit := String_map.add name (mask, called_funs) !current_unit

  let add_from_cmx map =
    List.iter
      (fun (name, mask) -> Misc.Stdlib.String.Tbl.replace registry name mask)
      map

  (* Functions that destroy all registers are left out: a missing entry
     means the same. *)
  let in_current_unit () =
    let all = Physical_register_mask.all () in
    let result =
      String_map.fold
        (fun name _ acc ->
           match destroyed_in_function name with
           | Some mask when mask <> all -> (name, mask) :: acc
           | Some _ | None -> acc
        )
        !current_unit
        []
    in
    List.rev result
end

let destroyed_at_oper : Mach.instruction_desc -> Reg.t array = function
  | Iop (Icall_imm { func }) as desc ->
      begin match Registry.destroyed_in_function func with
      | Some mask -> Physical_register_mask.to_array mask
      | None ->
          Proc.destroyed_at_oper desc
      end
  | desc ->
      Proc.destroyed_at_oper desc

let destroyed_transitive fname : Mach.instruction_desc -> _ = function
  | Iop (Icall_imm { func }) | Iop (Itailcall_imm { func }) when func = fname ->
      Physical_register_mask.empty, None
  | Iop (Icall_imm { func }) | Iop (Itailcall_imm { func }) ->
      begin match Registry.destroyed_in_function func with
      | Some mask -> mask, None
      | None -> Physical_register_mask.empty, Some func
      end
  | Iop Itailcall_ind ->
      Physical_register_mask.of_array (Proc.destroyed_at_oper (Iop Icall_ind)),
      None
  | Itrywith _ ->
      (* The handler can be reached through code that is not part of any
         function's register set: caml_raise_exn calling caml_stash_backtrace,
         C code raising, asynchronous exceptions. Execution then continues
         normally and can return to our caller. *)
      Physical_register_mask.of_array Proc.destroyed_at_raise, None
  | desc ->
      Physical_register_mask.of_array (Proc.destroyed_at_oper desc), None

let all_registers_destroyed (fundecl : Mach.fundecl) =
  let all = Physical_register_mask.all () in
  let mask, called_funs =
    Mach.instr_fold
      (fun (mask, called_funs) instr ->
         let mask = Physical_register_mask.add_array mask instr.res in
         let destroyed, called = destroyed_transitive fundecl.fun_name instr.desc in
         let called_funs =
           match called with
           | None -> called_funs
           | Some func -> String_set.add func called_funs
         in
         mask lor destroyed, called_funs
      )
      (Physical_register_mask.of_array Proc.destroyed_at_function_entry,
       String_set.empty)
      fundecl.fun_body
  in
  if mask = all then mask, String_set.empty else mask, called_funs

let fundecl fundecl =
  let destroyed, called_funs = all_registers_destroyed fundecl in
  Registry.add_from_current_unit fundecl.Mach.fun_name destroyed called_funs;
  fundecl

let max_register_pressure op =
  let default = Proc.max_register_pressure op in
  match op with
  | Mach.Icall_imm { func }->
      begin match Registry.destroyed_in_function func with
      | Some mask ->
          Array.mapi
            (fun class_ pressure ->
               pressure - Physical_register_mask.count_in_class mask class_)
            default
      | None ->
          Array.map (fun _ -> 0) default
      end
  | _ ->
      default

let safe_register_pressure op =
  match op with
  | Mach.Icall_imm _ -> 0
  | _ -> Proc.safe_register_pressure op
