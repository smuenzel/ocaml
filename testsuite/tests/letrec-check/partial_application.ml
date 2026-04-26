(* TEST
 expect;
*)

let f ~x:_ ~y:_ ~z:_ = ();;
[%%expect{|
val f : x:'a -> y:'b -> z:'c -> unit = <fun>
|}];;

(* Passing self immediately: forbidden *)
let rec x = f ~x;;
[%%expect{|
Line 1, characters 0-16:
1 | let rec x = f ~x;;
    ^^^^^^^^^^^^^^^^
Error: The following recursive definitions form a cycle: x-> x
|}];;

(* Passing self after an omitted argument: allowed *)
let rec y = f ~y;;
[%%expect{|
val y : x:'a -> z:'b -> unit = <fun>
|}];;

(* Passing self immediately: forbidden even if other arguments are omitted *)
let rec x = f ~x ~z:0;;
[%%expect{|
Line 1, characters 0-21:
1 | let rec x = f ~x ~z:0;;
    ^^^^^^^^^^^^^^^^^^^^^
Error: The following recursive definitions form a cycle: x-> x
|}];;

(* Calling self: allowed if the first argument is omitted *)
let g ~omitted ~given = fun ~given:_ -> given ~omitted
let rec f : omitted:_ -> given:_ -> _ = g ~given:(f ~given:0);;
[%%expect{|
val g : omitted:'a -> given:(omitted:'a -> 'b) -> given:'c -> 'b = <fun>
val f : omitted:'a -> given:int -> 'b = <fun>
|}];;

(* Calling self: forbidden if the first argument is passed *)
let g ~omitted_g ~given = fun ~omitted_f:_ ~given:_ -> given ~omitted_f:()
let rec f : omitted_g:_ -> omitted_f:_ -> given:_ -> _ =
  g ~given:(f ~omitted_g:() ~given:0);;
[%%expect{|
val g :
  omitted_g:'a ->
  given:(omitted_f:unit -> 'b) -> omitted_f:'c -> given:'d -> 'b = <fun>
Lines 2-3, characters 0-37:
2 | let rec f : omitted_g:_ -> omitted_f:_ -> given:_ -> _ =
3 |   g ~given:(f ~omitted_g:() ~given:0)..
Error: The following recursive definitions form a cycle: f-> f
|}];;
