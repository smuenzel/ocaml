
let (filename : string option ref) = ref None

let set_filename_exn new_filename =
  match !filename with
  | None -> filename := Some new_filename
  | Some _ -> failwith "log_perf filename already set"

exception Unknown_logging_scope of string

type scope =
  | Lps_cmm_div_int_const

let scope_to_string = function
  | Lps_cmm_div_int_const -> "cmm_div_int_const"

let logging_scope =
  lazy begin
    match Sys.getenv "CAML_PERF_LOG_SCOPE" with
    | exception Not_found -> Hashtbl.create 0
    | perf_log_scope ->
        let table = Hashtbl.create 17 in
        List.iter
          (fun scope ->
             let scope = 
               match String.lowercase_ascii scope with
               | "cmm_div_int_const" -> Lps_cmm_div_int_const
               | other -> raise (Unknown_logging_scope other)
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
