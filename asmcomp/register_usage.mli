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
  destroyed_in_function:(string -> Reg.Set.t option) -> Mach.fundecl ->
  Reg.Set.t
