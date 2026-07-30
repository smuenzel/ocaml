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
Error: The following recursive definitions form a cycle of
       non-statically constructive values (see manual section 12.1): x -> x
|}];;

let rec x = let u = [|y|] in 10. and y = 1.;;
[%%expect{|
Line 1, characters 0-32:
1 | let rec x = let u = [|y|] in 10. and y = 1.;;
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: In this recursive value definition, "y" must be evaluated before "x".
       Recursive values must be ordered such that values cannot be
       dereferenced before they are defined.
       The proposed order for this definition is: "y", "x"
|}];;
