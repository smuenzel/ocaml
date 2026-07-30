(* TEST
 expect;
*)

let rec a = lazy b and b = 3;;
[%%expect{|
Line 1, characters 0-18:
1 | let rec a = lazy b and b = 3;;
    ^^^^^^^^^^^^^^^^^^
Error: In this recursive value definition, "b" must be evaluated before "a".
       Recursive values must be ordered such that values cannot be
       dereferenced before they are defined.
       The proposed order for this definition is: "b", "a"
|}];;

let rec e = lazy (fun _ -> f) and f = ();;
[%%expect{|
val e : ('a -> unit) lazy_t = lazy <fun>
val f : unit = ()
|}];;

let rec x = lazy (Lazy.force x + Lazy.force x)
  ;;
[%%expect{|
val x : int Lazy.t = <lazy>
|}];;
