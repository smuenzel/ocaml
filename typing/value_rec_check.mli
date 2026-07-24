(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*               Jeremy Yallop, University of Cambridge                   *)
(*                                                                        *)
(*   Copyright 2017 Jeremy Yallop                                         *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

val is_valid_recursive_expression :
  Ident.t list ->
  Typedtree.expression ->
  Value_rec_types.recursive_binding_kind option

val is_valid_class_expr : Ident.t list -> Typedtree.class_expr -> bool

type 'payload sort_result =
  | Cycle_in_definition of 'payload * Ident.t list
  | Sorted_definition of (Ident.t
                          * Value_rec_types.recursive_binding_kind
                          * 'payload) list

val sort_value_bindings :
  (Ident.t * (Typedtree.expression * 'payload)) list ->
  'payload sort_result

val sort_class_expr :
  (Ident.t * (Typedtree.class_expr * 'payload)) list ->
  'payload sort_result
