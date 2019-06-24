open Cmm

module String = Misc.Stdlib.String
module V = Backend_var
module VP = Backend_var.With_provenance

type 'result shared_head =
  | Shend of 'result
  | Shop of operation * shparams * Debuginfo.t * 'result shared_head
and shparams =
  | Spnone
  | Spleft of expression
  | Spright of expression
  | Spmult of 
      { n_total : int
      ; n_left : int
      ; lefts : expression list
      ; rights : expression list
      }

let sparity = function
  | Spnone -> 1
  | Spleft _ | Spright _ -> 2
  | Spmult { n_total ; _} -> n_total

let params_to_arglist params next =
  match params with
  | Spnone -> [ next ]
  | Spleft left -> [ left ; next ]
  | Spright right -> [ next ; right ]
  | Spmult { lefts;  rights; _} ->
      List.concat [ lefts; [ next ]; rights ]

let rec sh_len = function
  | Shend _ -> 0
  | Shop (_,_,_,next) -> 1 + (sh_len next)

let _ = sh_len

type ash =
  | Asplain
  | Asop of operation * int *Debuginfo.t * ash

let rec ash_to_string = function
  | Asplain -> ""
  | Asop (op, arity, dbg, ash) ->
      Printf.sprintf 
        "/%s(%i)%s"
        (Printcmm.operation dbg op)
        arity
        (ash_to_string ash)

let log_ash ash name dbg =
  match ash with
  | Asplain -> ()
  | ash ->
    Log_perf.log_ext
      dbg
      Lps_cmm_shared_head
      (name ^ (ash_to_string ash))

let rec unshare_heads head =
  match head with
  | Shend result ->
      result
  | Shop (operation, params, dbg, next) ->
      let nexts = unshare_heads next in
      List.map 
        (fun next ->
           let arglist = params_to_arglist params next in
           Cop (operation, arglist, dbg)
        )
        nexts

let rec apply_shared_head ?from ash head ash_dbg f =
  match head with
  | Shend result ->
      let str =
        match from with
        | None -> "ASH"
        | Some from -> "ASH" ^ from
      in
      log_ash ash str ash_dbg;
      f result
  | Shop (operation, params, dbg, next) ->
      let next_ash = Asop (operation, (sparity params), dbg, ash) in
      let next = apply_shared_head ?from next_ash next ash_dbg f in
      let arglist = params_to_arglist params next in
      Cop (operation, arglist, dbg)

let apply_shared_head ?from head dbg f =
  apply_shared_head ?from Asplain head dbg f

let debug_combine dbg1 dbg2 =
  List.append dbg1 dbg2

let rec share_head_extend sh h =
  match sh, h with
  | Shend shs, h ->
      Shend (List.append shs [h])
  | Shop (operation, Spnone, dbg, next)
  , Cop(op2, [ o2p1 ], dbg2) ->
      if operation = op2 
      then begin
        let dbg = debug_combine dbg dbg2 in
        let next =
          share_head_extend next o2p1
        in
        Shop (operation, Spnone, dbg, next) 
      end 
      else begin
        let unshared_heads = unshare_heads next in
        Shend (List.append unshared_heads [h])
      end
  | Shop (operation, Spleft o1p1, dbg, next)
  , Cop(op2, [ o2p1; o2p2 ], dbg2) ->
      if operation = op2
      && Cmm.equal_no_dbg o1p1 o2p1
      then begin
        let dbg = debug_combine dbg dbg2 in
        let next =
          share_head_extend next o2p2
        in
        Shop (operation, Spleft o1p1, dbg, next) 
      end 
      else begin
        let unshared_heads = unshare_heads next in
        Shend (List.append unshared_heads [h])
      end
  | Shop(operation, Spright o1p2, dbg, next)
  , Cop(op2, [ o2p1; o2p2 ], dbg2) ->
      if operation = op2
      && Cmm.equal_no_dbg o1p2 o2p2
      then begin
        let dbg = debug_combine dbg dbg2 in
        let next =
          share_head_extend next o2p1
        in
        Shop (operation, Spright o1p2, dbg, next) 
      end 
      else begin
        let unshared_heads = unshare_heads next in
        Shend (List.append unshared_heads [h])
      end
  | Shop(operation, (Spmult { n_total; n_left; lefts; rights } as param) , dbg, next)
  , Cop(op2, o2p, dbg2) ->
      if operation = op2
      && (0 = List.compare_length_with o2p n_total)
      then begin
        let oleft,omid,oright =
          Misc.Stdlib.List.split3_at n_left o2p 
        in
        if List.for_all2 Cmm.equal_no_dbg lefts oleft
        && List.for_all2 Cmm.equal_no_dbg rights oright
        then begin
          let dbg = debug_combine dbg dbg2 in
          let next =
            share_head_extend next omid
          in
          Shop (operation, param , dbg, next) 
        end
        else begin
          let unshared_heads = unshare_heads next in
          Shend (List.append unshared_heads [h])
        end
      end 
      else begin
        let unshared_heads = unshare_heads next in
        Shend (List.append unshared_heads [h])
      end
  | sh, h ->
      let unshared_heads = unshare_heads sh in
      Shend (List.append unshared_heads [h])

let share_head_extend sh h =
  match share_head_extend sh h with
  | Shend _ -> None
  | other -> Some other

let rec share_head2 h1 h2 =
  match h1, h2 with
  | Cop(op1, [ o1p1 ], dbg1)
  , Cop(op2, [ o2p1 ], dbg2) ->
      if op1 = op2
      && (match op1 with | Cload _ -> false | _ -> true)
      then begin
        let dbg = debug_combine dbg1 dbg2 in
        let next = share_head2 o1p1 o2p1 in
        Shop(op1, Spnone, dbg, next)
      end
      else Shend [h1;h2]
  | Cop(op1, [ o1p1; o1p2 ], dbg1)
  , Cop(op2, [ o2p1; o2p2 ], dbg2) ->
      if op1 = op2
      then begin
        let dbg = debug_combine dbg1 dbg2 in
        if Cmm.equal_no_dbg o1p1 o2p1
        then begin
          (* TODO: Merge debug into equal expression *)
          let next2 = share_head2 o1p2 o2p2 in
          Shop(op1, Spleft o1p1, dbg, next2)
        end
        else if Cmm.equal_no_dbg o1p2 o2p2
        then begin
          let next1 = share_head2 o1p1 o2p1 in
          Shop(op1, Spright o1p2, dbg, next1)
        end
        else Shend [h1;h2]
      end
      else Shend [h1;h2]
  | Cop(op1, o1p, dbg1)
  , Cop(op2, o2p, dbg2) ->
      if op1 = op2
      then begin
        let dbg = debug_combine dbg1 dbg2 in
        try 
          let lefts, (mid1,mid2), rights =
            List.fold_left2 
              (fun acc o1p o2p ->
                 if Cmm.equal_no_dbg o1p o2p 
                 then begin
                   match acc with
                   | `Left acc ->
                       `Left (o1p :: acc)
                   | `Right (lefts, mid, rights) ->
                       `Right (lefts, mid, o1p :: rights)
                 end
                 else begin
                   match acc with
                   | `Left acc ->
                       `Right (List.rev acc, (o1p, o2p), [])
                   | `Right _ ->
                       raise_notrace Exit
                 end
              )
              (`Left [])
              o1p o2p 
            |> function
            | `Left _ -> raise_notrace Exit
            | `Right (lefts, mids, rev_rights) ->
                lefts, mids, List.rev rev_rights
          in
          let n_total = List.length o1p in
          let n_left = List.length lefts in
          let next2 = share_head2 mid1 mid2 in
          Shop (op1, Spmult {n_total; n_left; lefts; rights}, dbg, next2)
        with
        | Invalid_argument _
        | Exit -> Shend [h1;h2]
      end
      else Shend [h1;h2]
  | _, _ ->
      Shend [h1;h2]

let share_head2 h1 h2 =
  match share_head2 h1 h2 with
  | Shend _ -> None
  | other -> Some other

let debug_shared_head = false

let extract_shared_head_and_apply_tails from ~default tails inject_new_tails dbg =
  match tails with
  | [] -> default tails
  | _ :: [] -> default tails
  | tl1 :: tl2 :: tlrest ->
      begin match share_head2 tl1 tl2 with
      | None -> default tails
      | Some sh ->
          try
            let sh =
              List.fold_left
                (fun acc expr ->
                   match share_head_extend acc expr with
                   | None -> raise_notrace Exit
                   | Some sh -> sh
                )
                sh
                tlrest
            in
            let result =
              apply_shared_head ~from sh dbg inject_new_tails
            in
            if debug_shared_head
            then begin
              Printf.eprintf  "SHARE HEADER %s %i\n" from (sh_len sh);
              begin match dbg with
              | { Debuginfo. dinfo_file; dinfo_line; _ } :: _ -> 
                  Printf.eprintf "%s:%i\n" dinfo_file dinfo_line;
              | _ -> ()
              end;
            (*
            Printcmm.expression Format.str_formatter expr ;
            Printf.eprintf "expr=\n%s\n" (Format.flush_str_formatter ()) ;
               *)
              List.iteri
                (fun i exp ->
                   Printcmm.expression Format.str_formatter exp ;
                   Printf.eprintf "old%i=\n%s\n" i (Format.flush_str_formatter ()) ;
                )
                tails
              ;
              Printcmm.expression Format.str_formatter result;
              Printf.eprintf "new=\n%s\n\n" (Format.flush_str_formatter ()) ;
            end;
            result
          with 
          | Exit -> default tails
      end


let extract_shared_head from dbg expr =
  let tails, inject_new_tails = apply_tails expr in
  extract_shared_head_and_apply_tails
    from
    ~default:(fun _ -> expr) tails inject_new_tails dbg
