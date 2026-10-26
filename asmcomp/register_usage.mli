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

val all_registers_destroyed :
  Mach.fundecl ->
  Reg.Set.t

val destroyed_at_oper : Mach.instruction_desc -> Reg.t array

module Registry : sig
  val reset : unit -> unit
  val add_from_cmx : (string * int array) list -> unit
  val destroyed_in_function : string -> Reg.t array option
end
