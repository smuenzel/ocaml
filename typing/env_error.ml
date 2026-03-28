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

open Env

open Format_doc

(* Forward declarations *)

let print_path: Path.t printer ref = ref (fun _ _ -> assert false)
let pp_path ppf l = !print_path ppf l

module Style = Misc.Style

let quoted_longident = Style.as_inline_code Pprintast.Doc.longident
let quoted_constr = Style.as_inline_code Pprintast.Doc.constr

let spellcheck extract env lid =
  let choices ~path name = Misc.spellcheck (extract path env) name in
    match lid with
    | Longident.Lapply _ -> None
    | Longident.Lident s ->
       Misc.did_you_mean (choices ~path:None s)
    | Longident.Ldot (r, s) ->
       let pp ppf s =
         quoted_longident ppf (Longident.Ldot(r, Location.mknoloc s))
       in
       Misc.did_you_mean ~pp (choices ~path:(Some r.txt) s.txt)

let spellcheck_name extract env name =
  Misc.did_you_mean (Misc.spellcheck (extract env) name)

let extract_values path env =
  fold_values (fun name _ _ acc -> name :: acc) path env []
let extract_types path env =
  fold_types (fun name _ _ acc -> name :: acc) path env []
let extract_modules path env =
  fold_modules (fun name _ _ acc -> name :: acc) path env []
let extract_constructors path env =
  fold_constructors (fun desc acc -> desc.cstr_name :: acc) path env []
let extract_labels path env =
  fold_labels (fun desc acc -> desc.lbl_name :: acc) path env []
let extract_classes path env =
  fold_classes (fun name _ _ acc -> name :: acc) path env []
let extract_modtypes path env =
  fold_modtypes (fun name _ _ acc -> name :: acc) path env []
let extract_cltypes path env =
  fold_cltypes (fun name _ _ acc -> name :: acc) path env []
let extract_instance_variables env =
  fold_values
    (fun name _ descr acc ->
       match descr.val_kind with
       | Val_ivar _ -> name :: acc
       | _ -> acc) None env []


let report_lookup_error_doc loc env = function
  | Unbound_value(lid, hint) ->
      Location.aligned_error_hint ~loc
        "@{<ralign>Unbound value @}%a" quoted_longident lid
        (spellcheck extract_values env lid)
        ~sub:(
          match hint with
          | No_hint ->[]
          | Missing_rec def_loc ->
             let (_, line, _) =
               Location.get_pos_info def_loc.Location.loc_start
             in
             [Location.msg
                "@[@{<hint>Hint@}: If this is a recursive definition,@ \
                 you should add the %a keyword on line %i@]"
                Style.inline_code "rec"
                line
             ]
        )
  | Unbound_type lid ->
     Location.aligned_error_hint ~loc
       "@{<ralign>Unbound type constructor @}%a"
       quoted_longident lid
       (spellcheck extract_types env lid)
  | Unbound_module lid -> begin
      let main ppf =
        fprintf ppf "@{<ralign>Unbound module @}%a" quoted_longident lid in
      match find_modtype_by_name lid env with
      | exception Not_found ->
         Location.aligned_error_hint ~loc "%t" main
           (spellcheck extract_modules env lid)
      | _ ->
         Location.errorf ~loc "%t" main
           ~sub:[Location.msg
                   "@{<hint>Hint@}: There is a module type named %a,@ \
                    but module types are not modules"
                   quoted_longident lid
           ]
    end
  | Unbound_constructor lid ->
     Location.aligned_error_hint ~loc
       "@{<ralign>Unbound constructor @}%a"
       quoted_constr lid
       (spellcheck extract_constructors env lid)
  | Unbound_label lid ->
     Location.aligned_error_hint ~loc
       "@{<ralign>Unbound record field @}%a"
       quoted_longident lid
       (spellcheck extract_labels env lid)
  | Unbound_class lid -> begin
      let main ppf =
        fprintf ppf "@{<ralign>Unbound class @}%a" quoted_longident lid
      in
      match find_cltype_by_name lid env with
      | exception Not_found ->
         Location.aligned_error_hint ~loc "%t" main
           (spellcheck extract_classes env lid)
      | _ ->
         Location.errorf ~loc "%t" main
         ~sub:[
           Location.msg
             "@{<hint>Hint@}: There is a class type named %a,@ \
              but classes are not class types."
             quoted_longident lid
         ]
    end
  | Unbound_modtype lid -> begin
      let main ppf  =
        fprintf ppf "@{<ralign>Unbound module type @}%a"
          quoted_longident lid in
      match find_module_by_name lid env with
      | exception Not_found ->
         Location.aligned_error_hint ~loc "%t" main
           (spellcheck extract_modtypes env lid)
      | _ ->
         Location.errorf ~loc "%t" main
           ~sub:[
             Location.msg
               "@{<hint>Hint@}: There is a module named %a,@ \
                but modules are not module types"
               quoted_longident lid
           ]
      end
  | Unbound_cltype lid ->
     Location.aligned_error_hint ~loc
       "@{<ralign>Unbound class type @}%a" quoted_longident lid
      (spellcheck extract_cltypes env lid)
  | Unbound_instance_variable s ->
        Location.aligned_error_hint ~loc
          "@{<ralign>Unbound instance variable @}%a"
          Style.inline_code s
          (spellcheck_name extract_instance_variables env s)
  | Not_an_instance_variable s ->
     Location.aligned_error_hint ~loc
        "@{<ralign>The value @}%a is not an instance variable"
        Style.inline_code s
        (spellcheck_name extract_instance_variables env s)
  | Masked_instance_variable lid ->
      Location.errorf ~loc
        "The instance variable %a@ cannot@ be@ accessed@ from@ the@ \
         definition@ of@ another instance variable"
        quoted_longident lid
  | Masked_self_variable lid ->
      Location.errorf ~loc
        "The self variable %a@ cannot@ be@ accessed@ \
         from@ the@ definition of an instance variable"
        quoted_longident lid
  | Masked_ancestor_variable lid ->
      Location.errorf ~loc
        "The ancestor variable %a@ cannot@ be@ accessed@ from@ \
         the definition of an instance variable"
        quoted_longident lid
  | Illegal_reference_to_recursive_module { container; unbound } ->
      let container = Option.value ~default:"_" container in
      let self_or_definition, self_or_unbound =
        if String.equal container unbound
        then dprintf "its own definition", dprintf "itself"
        else
          dprintf "the definition of the module %a" Style.inline_code container,
          dprintf "the module type of %a" Style.inline_code unbound
      in
      Location.errorf ~loc
        "@[<hov>This module type is recursive.@ \
         This use of the recursive module %a@ \
         within %t@ \
         makes the module type of %a depend on@ %t.@ \
         Such recursive definitions of module types are not allowed.@]"
        Style.inline_code unbound
        self_or_definition
        Style.inline_code container
        self_or_unbound
  | Illegal_reference_to_recursive_class_type
      { container; unbound; unbound_class_type; container_class_type } ->
      let container = Option.value ~default:"_" container in
      let self_or_unbound =
        if String.equal container unbound
        then dprintf "itself"
        else dprintf "the module type of %a" Style.inline_code unbound
      in
      Location.errorf ~loc
        "@[<hov>This class type is recursive.@ This use of the class type %a@ \
         from the recursive module %a@ within the definition of@ \
         the class type %a@ in the recursive module %a@ \
         makes the module type of %a@ depend on %t.@ \
         Such recursive definitions of@ class types within recursive modules@ \
         are not allowed.@]"
        quoted_longident unbound_class_type
        Style.inline_code unbound
        Style.inline_code container_class_type
        Style.inline_code container
        Style.inline_code container
        self_or_unbound
  | Structure_used_as_functor lid ->
     Location.errorf ~loc
       "The module %a is a structure, it cannot be applied"
        quoted_longident lid
  | Abstract_used_as_functor lid ->
     Location.errorf ~loc
       "The module %a is abstract, it cannot be applied"
       quoted_longident lid
  | Functor_used_as_structure lid ->
     Location.errorf ~loc
       "The module %a is a functor, it cannot have any components"
       quoted_longident lid
  | Abstract_used_as_structure lid ->
     Location.errorf ~loc
       "The module %a is abstract, it cannot have any components"
       quoted_longident lid
  | Generative_used_as_applicative lid ->
     Location.errorf ~loc
       "The functor %a is generative,@ it@ cannot@ be@ \
        applied@ in@ type@ expressions"
        quoted_longident lid
  | Cannot_scrape_alias(lid, p) ->
      let cause =
        if Current_unit.Name.is_path p then "is the current compilation unit"
        else "is missing"
      in
      Location.errorf ~loc
        "The module %a is an alias for module %a, which %s"
        quoted_longident lid
        (Style.as_inline_code pp_path) p cause

let report_error_doc = function
  | Missing_module(loc, path1, path2) ->
     let pp_path path1 path2 ppf =
      if Path.same path1 path2 then
        fprintf ppf "Internal path@ %a@ is dangling."
          Style.inline_code (Path.name path1)
      else
        fprintf ppf "Internal path@ %a@ expands to@ %a@ which is dangling."
          Style.inline_code (Path.name path1)
          Style.inline_code (Path.name path2);
     in
     Location.errorf ~loc
       "%t@ @[The compiled interface for module@ %a@ was not found.@]"
        (pp_path path1 path2)
        Style.inline_code (Ident.name (Path.head path2))
  | Illegal_value_name(loc, name) ->
      Location.errorf ~loc "%a is not a valid value identifier."
       Style.inline_code name
  | Lookup_error(loc, t, err) -> report_lookup_error_doc loc t err

let () =
  Location.register_error_of_exn
    (function
      | Error err ->  Some (report_error_doc err)
      | _ ->
          None
    )
