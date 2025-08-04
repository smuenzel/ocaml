(* TEST
 expect;
*)

type _ t1 =
  | A : 'a -> [> `A of 'a ] t1
  | B : 'a -> [> `B of 'a ] t1

let f1 (type a) (t : [ `A of a | `B of a ] t1) = assert false

type t = T : _ t1 -> t

let f (T x) =
  match x with
  | (A _ | B _) as x -> ignore (f1 x : _)

[%%expect{|
type _ t1 = A : 'a -> [> `A of 'a ] t1 | B : 'a -> [> `B of 'a ] t1
val f1 : [ `A of 'a | `B of 'a ] t1 -> 'b = <fun>
type t = T : 'a t1 -> t
Line 11, characters 7-8:
11 |   | (A _ | B _) as x -> ignore (f1 x : _)
            ^
Error: This pattern matches values of type "$1"
       but a pattern was expected which matches values of type "'a"
       The type constructor "$1" would escape its scope
       Type "$1" is abstract because no corresponding cmi file was found
       in path.
|}]


type _ t1 =
  | A : 'a -> [> `A of 'a ] t1
  | B : 'a -> [> `B of 'a ] t1

type t = T : _ t1 -> t

let f (T (type a) (x : a t1)) =
  match x with
  | (A _ | B _) as x -> ()

[%%expect{|
type _ t1 = A : 'a -> [> `A of 'a ] t1 | B : 'a -> [> `B of 'a ] t1
type t = T : 'a t1 -> t
Line 9, characters 7-8:
9 |   | (A _ | B _) as x -> ()
           ^
Error: This pattern matches values of type "$1"
       but a pattern was expected which matches values of type "'a"
       The type constructor "$1" would escape its scope
       Type "$1" is abstract because no corresponding cmi file was found
       in path.
|}]
