
let (filename : string option ref) = ref None

let set_filename_exn new_filename =
  match !filename with
  | None -> filename := Some new_filename
  | Some _ -> failwith "log_perf filename already set"

exception Unknown_logging_scope of string

type scope =
  | Lps_cmm_div_int_const
  | Lps_cmm_simp_nested_cmp
  | Lps_cmm_simp_nested_eq_1
  | Lps_cmm_simp_nested_eq_3
  | Lps_cmm_simp_nested_neq_0
  | Lps_cmm_simp_tag_and
  | Lps_cmm_simp_tag_or
  | Lps_cmm_simp_tag_xor

let conversion_table =
  [ Lps_cmm_div_int_const, "cmm_div_int_const"
  ; Lps_cmm_simp_nested_cmp, "cmm_simp_nested_cmp"
  ; Lps_cmm_simp_nested_eq_1, "cmm_simp_nested_eq1"
  ; Lps_cmm_simp_nested_eq_3, "cmm_simp_nested_eq3"
  ; Lps_cmm_simp_nested_neq_0, "cmm_simp_nested_neq0"
  ; Lps_cmm_simp_tag_and, "cmm_simp_tag_and"
  ; Lps_cmm_simp_tag_or, "cmm_simp_tag_or"
  ; Lps_cmm_simp_tag_xor, "cmm_simp_tag_xor"
  ]

let scope_to_string scope =
  List.find
    (fun (scope',_) -> scope = scope')
    conversion_table
  |> snd

let logging_scope =
  lazy begin
    match Sys.getenv "CAML_PERF_LOG_SCOPE" with
    | exception Not_found -> Hashtbl.create 0
    | perf_log_scope ->
        let table = Hashtbl.create 17 in
        List.iter
          (fun scope ->
             let scope = String.lowercase_ascii scope in
             match scope with
             | "all" ->
                 List.iter
                   (fun (scope,_) -> Hashtbl.add table scope ())
                   conversion_table
             | _ ->
                 let scope = 
                   match List.find_opt (fun (_,str') -> scope = str') conversion_table with
                   | None ->
                       raise (Unknown_logging_scope scope)
                   | Some (scope,_) -> scope
                 in
                 Hashtbl.add table scope ()
          )
          (String.split_on_char ',' perf_log_scope)
        ;
        table
  end

let logging_file =
  lazy begin
    let l_filename =
      let source_filename =
        match !filename with
        | None -> "no-file"
        | Some filename -> filename
      in
      let id = Hashtbl.hash source_filename in
      let time = Random.int 10000 in
      let tmpdir =
        match Sys.getenv "TMPDIR" with
        | exception Not_found -> "/tmp"
        | tmpdir -> tmpdir
      in
      Printf.sprintf "%s/ocaml_perf_%i_%i.log" tmpdir id time
    in
    open_out l_filename
  end

let abbrev_debug_info = function
  | [] -> "unknown"
  | dbg :: _ -> Debuginfo.to_string [ dbg ]

let log dbg event =
  if Hashtbl.mem (Lazy.force logging_scope) event
  then begin
    Printf.fprintf (Lazy.force logging_file)
      "%s:%s\n"
      (scope_to_string event)
      (abbrev_debug_info dbg)
  end
