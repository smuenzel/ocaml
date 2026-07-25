(* TEST
 expect;
*)
type t = { x : int; self : t };;
[%%expect {|
type t = { x : int; self : t; }
|}];;

module S = struct
  let rec x = 1
  and u = Some { t with x = 2 }
  and t = { x; self = t }
  (* We have carefully placed `u` before `t` here,
     so that the copy { t with .. }, if accepted,
     is evaluated before 't' is initialized -- making
     the assertion below fail, typically aborting
     with a segmentation fault.

     If you exchange the declaration orders of `u` and `t`,
     and the static check accepts this example, then `t`
     is initialized first and the assertion succeeds. *)


  let () = match u with
    | None -> assert false
    | Some {x = _; self} -> assert (self.x = t.x)
end;;
[%%expect {|
Line 4, characters 2-25:
4 |   and t = { x; self = t }
      ^^^^^^^^^^^^^^^^^^^^^^^
Error: The following recursive definitions form a cycle of
       non-statically constructive values (see manual section 12.1):
       t -> u -> u
|}];;
