(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 2021 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

type t = in_channel

type open_flag = Stdlib.open_flag =
  | Open_rdonly
  | Open_wronly
  | Open_append
  | Open_creat
  | Open_trunc
  | Open_excl
  | Open_binary
  | Open_text
  | Open_nonblock

let stdin = Stdlib.stdin
let open_bin = Stdlib.open_in_bin
let open_text = Stdlib.open_in
let open_gen = Stdlib.open_in_gen

let with_open openfun s f =
  let ic = openfun s in
  Fun.protect ~finally:(fun () -> Stdlib.close_in_noerr ic)
    (fun () -> f ic)

let with_open_bin s f =
  with_open Stdlib.open_in_bin s f

let with_open_text s f =
  with_open Stdlib.open_in s f

let with_open_gen flags perm s f =
  with_open (Stdlib.open_in_gen flags perm) s f

let seek = Stdlib.LargeFile.seek_in
let pos = Stdlib.LargeFile.pos_in
let length = Stdlib.LargeFile.in_channel_length
let close = Stdlib.close_in
let close_noerr = Stdlib.close_in_noerr

let input_char ic =
  match Stdlib.input_char ic with
  | c -> Some c
  | exception End_of_file -> None

let input_byte ic =
  match Stdlib.input_byte ic with
  | n -> Some n
  | exception End_of_file -> None

let input_line ic =
  match Stdlib.input_line ic with
  | s -> Some s
  | exception End_of_file -> None

let input = Stdlib.input

external unsafe_input_bigarray :
  t -> _ Bigarray.Array1.t -> int -> int -> int
  = "caml_ml_input_bigarray"

let input_bigarray ic buf ofs len =
  if ofs < 0 || len < 0 || ofs > Bigarray.Array1.dim buf - len
  then invalid_arg "input_bigarray"
  else unsafe_input_bigarray ic buf ofs len

let really_input ic buf pos len =
  match Stdlib.really_input ic buf pos len with
  | () -> Some ()
  | exception End_of_file -> None

let rec unsafe_really_input_bigarray ic buf ofs len =
  if len <= 0 then Some () else begin
    let r = unsafe_input_bigarray ic buf ofs len in
    if r = 0
    then None
    else unsafe_really_input_bigarray ic buf (ofs + r) (len - r)
  end

let really_input_bigarray ic buf ofs len =
  if ofs < 0 || len < 0 || ofs > Bigarray.Array1.dim buf - len
  then invalid_arg "really_input_bigarray"
  else unsafe_really_input_bigarray ic buf ofs len

let really_input_string ic len =
  match Stdlib.really_input_string ic len with
  | s -> Some s
  | exception End_of_file -> None

(* Read up to [len] bytes into [buf], starting at [ofs]. Return total bytes
   read. *)
let read_upto ic buf ofs len =
  let rec loop ofs len =
    if len = 0 then ofs
    else begin
      let r = Stdlib.input ic buf ofs len in
      if r = 0 then
        ofs
      else
        loop (ofs + r) (len - r)
    end
  in
  loop ofs len - ofs

let input_all_rev_list ic =
  let rec read_one_chunk_at_a_time ic ~acc ~total_size =
    let chunk_size = Sys.io_buffer_size in
    let buf = Bytes.create chunk_size in
    let nread = read_upto ic buf 0 chunk_size in
    let total_size = total_size + nread in
    let acc = buf :: acc in
    if nread < chunk_size then
      acc, total_size
    else
      read_one_chunk_at_a_time ic ~acc ~total_size
  in
  read_one_chunk_at_a_time ic ~acc:[] ~total_size:0

module type Input_all_param = sig
  type temporary
  type result
  val max_size : int
  val blit : Bytes.t -> int -> temporary -> int -> int -> unit
  val create : int -> temporary
  val finalize : temporary -> result
end

module Make_input_all(P : Input_all_param) = struct
  let input_all ic =
    let acc_rev, total_size = input_all_rev_list ic in
    if total_size > P.max_size then
      invalid_arg "input_all";
    let total_buf = P.create total_size in
    (* Final buffer may be shorter than buffer size *)
    let number_of_full_buffers = total_size / Sys.io_buffer_size in
    let final_buffer_size = total_size mod Sys.io_buffer_size in
    let acc_rev =
      match acc_rev with
      | [] -> acc_rev
      | buf :: acc_rev ->
          P.blit buf
            0 total_buf
            (Sys.io_buffer_size * number_of_full_buffers) final_buffer_size;
          acc_rev
    in
    let rec loop acc_rev ~i =
      match acc_rev with
      | [] -> P.finalize total_buf
      | buf :: acc_rev ->
          P.blit buf 0 total_buf (i * Sys.io_buffer_size) Sys.io_buffer_size;
          loop acc_rev ~i:(i - 1)
    in
    loop acc_rev ~i:(number_of_full_buffers - 1)
end

module Input_all_bytes =
  Make_input_all(struct
    type temporary = Bytes.t
    type result = string
    let max_size = Sys.max_string_length
    let blit = Bytes.blit
    let create = Bytes.create
    let finalize = Bytes.unsafe_to_string
  end)

let input_all = Input_all_bytes.input_all

module Input_all_bigarray =
  Make_input_all(struct
    type temporary = (char, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t
    type result = temporary
    let max_size = Int.max_int
    let blit src src_pos dest dst_pos element_count =
      Bigarray.Genarray.blit_from_bytes src ~src_pos (Bigarray.genarray_of_array1 dest) ~dst_pos ~element_count
    let create = Bigarray.Array1.create Bigarray.Char Bigarray.C_layout
    let finalize ba = ba
  end)

let input_all_bigarray = Input_all_bigarray.input_all

let [@tail_mod_cons] rec input_lines ic =
  match Stdlib.input_line ic with
  | line -> line :: input_lines ic
  | exception End_of_file -> []

let rec fold_lines f accu ic =
  match Stdlib.input_line ic with
  | line -> fold_lines f (f accu line) ic
  | exception End_of_file -> accu

let set_binary_mode = Stdlib.set_binary_mode_in

external is_binary_mode : in_channel -> bool = "caml_ml_is_binary_mode"

external isatty : t -> bool = "caml_sys_isatty"
