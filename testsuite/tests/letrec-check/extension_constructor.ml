(* TEST
 expect;
*)

(* Example from Stephen Dolan.
   Accessing an extension constructor involves accessing the module
   in which it's defined.
 *)
module type T =
  sig exception A of int end;;
[%%expect{|
module type T = sig exception A of int end
|}];;

let rec x =
  let module M = (val m) in
  M.A 42
and (m : (module T)) =
  (module (struct exception A of int end) : T);;
[%%expect{|
Lines 1-3, characters 0-8:
1 | let rec x =
2 |   let module M = (val m) in
3 |   M.A 42
Error: In this recursive value definition, "m" must be evaluated before "x".
       Recursive values must be ordered such that values cannot be
       dereferenced before they are defined.
       The proposed order for this definition is: "m", "x"
|}];;
