(* TEST
 expect;
*)

let f ~x () = x ();;
[%%expect{|
val f : x:(unit -> 'a) -> unit -> 'a = <fun>
|}];;

let rec x = f ~x;;
[%%expect{|
Line 1, characters 0-16:
1 | let rec x = f ~x;;
    ^^^^^^^^^^^^^^^^
Error: This recursive definition forms a cycle of
       non-statically constructive values (see manual section 12.1).
Trace: "x" dereferences "x"
|}];;

let f x ~y = x + y
(* this function creates "abstracted arguments" in the sense of
   Rec_check.is_abstracted_arg. Those should be treated as
   returned/unguarded, and not delayed, otherwise the code below
   segfaults. *)
let rec g = f ~y:(print_endline !y; 0)
and y =
  let _ = g in (* ignore g to have a real dependency *)
  ref "foo";;
[%%expect {|
val f : int -> y:int -> int = <fun>
Lines 7-9, characters 0-11:
7 | and y =
8 |   let _ = g in (* ignore g to have a real dependency *)
9 |   ref "foo"..
Error: This recursive definition forms a cycle of
       non-statically constructive values (see manual section 12.1).
Trace: "g" dereferences "y"
Trace: "y" dereferences "g"
Trace: "g" dereferences "y"
|}]
