(* TEST
 expect;
*)

(* This program is a minimal example which segfault if
   (e1.x <- e2) considers that (e2) is in Return mode,
   rather than Dereference -- here a write to a
   field in a statically-known all-float record is
   unboxed on the flight, so accepting this example
   would dereference (when running `g.f <- y` with y
   uninitialized) an arbitrary address. *)
type t = { mutable f: float }
let g = { f = 0.0 }
let rec x = (g.f <- y; ()) and y = 2.0;;
[%%expect{|
type t = { mutable f : float; }
val g : t = {f = 0.}
val y : float = 2.
val x : unit = ()
|}];;

(* same example, with object instance variables
   instead of record fields *)
module S = struct
  class c = object
    val mutable f = 0.0
    method m =
      let rec x = (f <- y; ()) and y = 2.0 in f
  end
  let _ = print_float (new c)#m
end
[%%expect{|
Line 5, characters 14-15:
5 |       let rec x = (f <- y; ()) and y = 2.0 in f
                  ^
Warning 26 [unused-var]: unused variable "x".

Line 5, characters 35-36:
5 |       let rec x = (f <- y; ()) and y = 2.0 in f
                                       ^
Warning 26 [unused-var]: unused variable "y".

module S :
  sig class c : object val mutable f : float method m : float end end
|}];;
