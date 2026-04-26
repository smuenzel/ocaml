(* TEST
 flat-float-array;
 expect;
*)

let rec x = [| x |]; 1.;;
[%%expect{|
Line 1, characters 12-19:
1 | let rec x = [| x |]; 1.;;
                ^^^^^^^
Warning 10 [non-unit-statement]: this expression should have type unit.

Line 1, characters 0-23:
1 | let rec x = [| x |]; 1.;;
    ^^^^^^^^^^^^^^^^^^^^^^^
Error: The following recursive definitions form a cycle: x-> x
|}];;

let rec x = let u = [|y|] in 10. and y = 1.;;
[%%expect{|
Line 1, characters 16-17:
1 | let rec x = let u = [|y|] in 10. and y = 1.;;
                    ^
Warning 26 [unused-var]: unused variable "u".

val y : float = 1.
val x : float = 10.
|}];;
