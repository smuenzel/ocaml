(* TEST
 expect;
*)

class c = object end
let rec x = fun () -> new c;;
[%%expect{|
class c : object  end
val x : unit -> c = <fun>
|}];;

class c _ = object end
let rec x = new c x;;
[%%expect{|
class c : 'a -> object  end
Line 2, characters 0-19:
2 | let rec x = new c x;;
    ^^^^^^^^^^^^^^^^^^^
Error: The following recursive definitions form a cycle of
       non-statically constructive values (see manual section 12.1): x-> x
|}];;

let rec x = y#m and y = object method m = () end;;
[%%expect{|
val y : < m : unit > = <obj>
val x : unit = ()
|}];;

let rec x = (object method m _ = () end)#m x;;
[%%expect{|
Line 1, characters 0-44:
1 | let rec x = (object method m _ = () end)#m x;;
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The following recursive definitions form a cycle of
       non-statically constructive values (see manual section 12.1): x-> x
|}];;

let rec x = object val mutable v = 0 method m = v <- y end and y = 1;;
[%%expect{|
val y : int = 1
val x : < m : unit > = <obj>
|}];;

let rec x = object method m = x end;;
[%%expect{|
Line 1, characters 0-35:
1 | let rec x = object method m = x end;;
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The following recursive definitions form a cycle of
       non-statically constructive values (see manual section 12.1): x-> x
|}];;

let rec x = object method m = ignore x end;;
[%%expect{|
Line 1, characters 0-42:
1 | let rec x = object method m = ignore x end;;
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The following recursive definitions form a cycle of
       non-statically constructive values (see manual section 12.1): x-> x
|}];;
