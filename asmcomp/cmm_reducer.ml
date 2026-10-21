open Cmm

module V = Backend_var
module VP = Backend_var.With_provenance

(* Remove single-use pure variables *)
module Cleanup_cmm = struct
  type var_usage =
    | Unused
    | Exactly_once
    | Many

  type var_def =
    { depth : int
    ; mutable usage : var_usage
    }

  type usages = var_def V.Tbl.t

  let register_one_use ~ccatch_depth tbl var =
    match V.Tbl.find_opt tbl var with
    | None -> ()
    | Some var_def ->
        if var_def.depth < ccatch_depth then var_def.usage <- Many
        else
          match var_def.usage with
          | Unused -> var_def.usage <- Exactly_once
          | Exactly_once -> var_def.usage <- Many
          | Many -> ()

  let rec find_usages ~ccatch_depth (tbl : usages) = function
    | Cvar_mut _ ->
        (* We don't care about mutable variables *)
        ()
    | Clet (id, Cpure (defn), body) ->
        V.Tbl.add tbl (VP.var id) { depth = ccatch_depth; usage = Unused };
        find_pure_usages ~ccatch_depth tbl defn;
        find_usages ~ccatch_depth tbl body
    | Clet (_id, defn, body) ->
        find_usages ~ccatch_depth tbl defn;
        find_usages ~ccatch_depth tbl body
    | Clet_mut (_id, _, defn, body) ->
        find_pure_usages ~ccatch_depth tbl defn;
        find_usages ~ccatch_depth tbl body
    | Cphantom_let (_id, _defn, body) ->
        find_usages ~ccatch_depth tbl body
    | Cifthenelse (cond, _ifso_dbg, ifso, _ifnot_dbg, ifnot, _dbg) ->
        find_pure_usages ~ccatch_depth tbl cond;
        find_usages ~ccatch_depth tbl ifso;
        find_usages ~ccatch_depth tbl ifnot
    | Csequence (e1, e2) ->
        find_usages ~ccatch_depth tbl e1;
        find_usages ~ccatch_depth tbl e2
    | Cswitch (e, _tbl, el, _dbg') ->
        find_pure_usages ~ccatch_depth tbl e;
        Array.iter (fun (e, _dbg) -> find_usages ~ccatch_depth tbl e) el
    | Ccatch (rec_flag, handlers, body) ->
        List.iter (fun (_n, _ids, handler, _dbg) ->
            find_usages
              ~ccatch_depth:(ccatch_depth + match rec_flag with Recursive -> 1 | Nonrecursive -> 0)
              tbl handler) handlers;
        find_usages ~ccatch_depth tbl body
    | Ctrywith (e1, _id, e2, _dbg) ->
        find_usages ~ccatch_depth tbl e1;
        find_usages ~ccatch_depth tbl e2
    | Cassign (_id, e) ->
        find_pure_usages ~ccatch_depth tbl e
    | Cop (_op, el, _dbg) ->
        List.iter (find_pure_usages ~ccatch_depth tbl) el
    | Cexit (_n, el) ->
        List.iter (find_pure_usages ~ccatch_depth tbl) el
    | Cpure e ->
        find_pure_usages ~ccatch_depth tbl e
  and find_pure_usages ~ccatch_depth tbl = function
    | Cconst_int _
    | Cconst_natint _
    | Cconst_float _
    | Cconst_symbol _ -> ()
    | Cvar id ->
        register_one_use ~ccatch_depth tbl id
    | Ctuple lst ->
        List.iter (find_pure_usages ~ccatch_depth tbl) lst
    | Cpure_op (_, lst, _) ->
        List.iter (find_pure_usages ~ccatch_depth tbl) lst
    | Cpure_let (id, defn, body) ->
        V.Tbl.add tbl (VP.var id) { depth = ccatch_depth; usage = Unused };
        find_pure_usages ~ccatch_depth tbl defn;
        find_pure_usages ~ccatch_depth tbl body
    | Cpure_ifthenelse (cond, ifso, ifnot) ->
        find_pure_usages ~ccatch_depth tbl cond;
        find_pure_usages ~ccatch_depth tbl ifso;
        find_pure_usages ~ccatch_depth tbl ifnot
    | Creturn_addr -> ()

  let rec subst (tbl : usages) (defs: Cmm.pure_expression V.Map.t) cmm =
    match cmm with
    | Cvar_mut _ -> cmm
    | Clet (id, Cpure (defn), body) ->
        begin match V.Tbl.find_opt tbl (VP.var id) with
        | Some { usage = Exactly_once } ->
            let defn' = subst_pure tbl defs defn in
            let defs = V.Map.add (VP.var id) defn' defs in
            let res = subst tbl defs body in
            res
        | Some { usage = Unused } ->
            let res = subst tbl defs body in
            res
        | _ ->
            let defn' = subst_pure tbl defs defn in
            let res = subst tbl defs body in
            match res with
            | Cpure e ->
                Cpure (Cpure_let(id, defn', e))
            | _ ->
                if defn == defn' && res == body then cmm
                else Clet (id, Cpure (defn'), res)
        end
    | Clet (id, defn, body) ->
        let defn' = subst tbl defs defn in
        let res = subst tbl defs body in
        if defn == defn' && res == body then cmm
        else Clet (id, defn', res)
    | Clet_mut (id, kind, defn, body) ->
        let defn' = subst_pure tbl defs defn in
        let res = subst tbl defs body in
        if defn == defn' && res == body then cmm
        else Clet_mut (id, kind, defn', res)
    | Cphantom_let (id, defn, body) ->
        let res = subst tbl defs body in
        if res == body then cmm
        else Cphantom_let (id, defn, res)
    | Cifthenelse (cond, ifso_dbg, ifso, ifnot_dbg, ifnot, dbg) ->
        let cond' = subst_pure tbl defs cond in
        let ifso' = subst tbl defs ifso in
        let ifnot' = subst tbl defs ifnot in
        if cond == cond' && ifso == ifso' && ifnot == ifnot' then cmm
        else Cifthenelse (cond', ifso_dbg, ifso', ifnot_dbg, ifnot', dbg)
    | Csequence (e1, e2) ->
        let e1' = subst tbl defs e1 in
        let e2' = subst tbl defs e2 in
        if e1 == e1' && e2 == e2' then cmm
        else Csequence (e1', e2')
    | Cswitch (e, swtbl, el, dbg') ->
        let e' = subst_pure tbl defs e in
        (* CR smuenzel: Array.map doesn't return the original array *)
        let el' = Array.map (fun (e, dbg) -> subst tbl defs e, dbg) el in
        if e == e' && el == el' then cmm
        else Cswitch (e', swtbl, el', dbg')
    | Ccatch (rec_flag, handlers, body) ->
        (* CR smuenzel: do we want to move variables into the loop?
           Could lead to duplicate evaluation inside the loop *)
        let map_h ((n, ids, handler, dbg) as h) =
          let handler' = subst tbl defs handler in
          if handler == handler' then h
          else (n, ids, handler', dbg)
        in
        (* CR smuenzel: List.map doesn't return the original list *)
        let handlers' = List.map map_h handlers in
        let body' = subst tbl defs body in
        if handlers == handlers' && body == body' then cmm
        else Ccatch (rec_flag, handlers', body')
    | Ctrywith (e1, id, e2, dbg) ->
        let e1' = subst tbl defs e1 in
        let e2' = subst tbl defs e2 in
        if e1 == e1' && e2 == e2' then cmm
        else Ctrywith (e1', id, e2', dbg)
    | Cassign (id, e) ->
        let e' = subst_pure tbl defs e in
        if e == e' then cmm
        else Cassign (id, e')
    | Cop (op, el, dbg) ->
        let el' = List.map (subst_pure tbl defs) el in
        if el == el' then cmm
        else Cop (op, el', dbg)
    | Cexit (n, el) ->
        (* CR smuenzel: List.map doesn't return the original list *)
        let el' = List.map (subst_pure tbl defs) el in
        if el == el' then cmm
        else Cexit (n, el')
    | Cpure e ->
        let e' = subst_pure tbl defs e in
        if e == e' then cmm
        else Cpure e'
  and subst_pure (tbl : usages) (defs: Cmm.pure_expression V.Map.t) cmm =
    match cmm with
    | Cvar id ->
        begin match V.Map.find_opt id defs with
        | Some defn -> defn
        | None -> cmm
        end
    | Ctuple lst ->
        Ctuple (List.map (subst_pure tbl defs) lst)
    | Cpure_op (op, lst, dbg) ->
        Cpure_op(op, List.map (subst_pure tbl defs) lst, dbg)
    | Cpure_let (id, defn, body) ->
        begin match V.Tbl.find_opt tbl (VP.var id) with
        | Some { usage = Exactly_once } ->
            let defn' = subst_pure tbl defs defn in
            let defs = V.Map.add (VP.var id) defn' defs in
            let body' = subst_pure tbl defs body in
            body'
        | Some { usage = Unused } ->
            let body' = subst_pure tbl defs body in
            body'
        | _ ->
            let defn' = subst_pure tbl defs defn in
            let body' = subst_pure tbl defs body in
            if defn == defn' && body == body' then cmm
            else Cpure_let(id, defn', body')
        end
    | Cpure_ifthenelse (cond, ifso, ifnot) ->
        let cond' = subst_pure tbl defs cond in
        let ifso' = subst_pure tbl defs ifso in
        let ifnot' = subst_pure tbl defs ifnot in
        if cond == cond' && ifso == ifso' && ifnot == ifnot' then cmm
        else Cpure_ifthenelse(cond', ifso', ifnot')
    | Cconst_int _ | Cconst_natint _ | Cconst_float _ | Cconst_symbol _ -> cmm
    | Creturn_addr -> cmm
end

let cleanup_cmm cmm =
  let tbl = V.Tbl.create 11 in
  Cleanup_cmm.find_usages ~ccatch_depth:0 tbl cmm;
  Cleanup_cmm.subst tbl V.Map.empty cmm


let reduce x = cleanup_cmm x
