(* TEST
 expect;
*)

type r = R of r list [@@unboxed]
let rec a = R [a];;
[%%expect{|
type r = R of r list [@@unboxed]
val a : r = R [<cycle>]
|}];;


type t = {x: int64} [@@unboxed]
let rec x = {x = y} and y = 3L;;
[%%expect{|
type t = { x : int64; } [@@unboxed]
val y : int64 = 3L
val x : t = {x = 3L}
|}];;

type r = A of r [@@unboxed]
let rec y = A y;;
[%%expect{|
type r = A of r [@@unboxed]
Line 2, characters 0-15:
2 | let rec y = A y;;
    ^^^^^^^^^^^^^^^
Error: The following recursive definitions form a cycle of
       non-statically constructive values (see manual section 12.1): y-> y
|}];;

(* This test is not allowed if 'a' is unboxed, but should be accepted
   as written *)
type a = {a: b}
and b = X of a | Y

let rec a =
  {a=
    (if Sys.opaque_identity true then
       X a
     else
       Y)};;
[%%expect{|
type a = { a : b; }
and b = X of a | Y
val a : a = {a = X <cycle>}
|}];;

type a = {a: b }[@@unboxed]
and b = X of a | Y

let rec a =
  {a=
    (if Sys.opaque_identity true then
       X a
     else
       Y)};;
[%%expect{|
type a = { a : b; } [@@unboxed]
and b = X of a | Y
Lines 4-9, characters 0-10:
4 | let rec a =
5 |   {a=
6 |     (if Sys.opaque_identity true then
7 |        X a
8 |      else
9 |        Y)}..
Error: The following recursive definitions form a cycle of
       non-statically constructive values (see manual section 12.1): a-> a
|}];;

(* This test is not allowed if 'c' is unboxed, but should be accepted
   as written *)
type d = D of e
and e = V of d | W;;
[%%expect{|
type d = D of e
and e = V of d | W
|}];;

let rec d =
  D
    (if Sys.opaque_identity true then
       V d
     else
       W);;
[%%expect{|
val d : d = D (V <cycle>)
|}];;

type d = D of e [@@unboxed]
and e = V of d | W;;

let rec d =
  D
    (if Sys.opaque_identity true then
       V d
     else
       W);;
[%%expect{|
type d = D of e [@@unboxed]
and e = V of d | W
Lines 4-9, characters 0-9:
4 | let rec d =
5 |   D
6 |     (if Sys.opaque_identity true then
7 |        V d
8 |      else
9 |        W)..
Error: The following recursive definitions form a cycle of
       non-statically constructive values (see manual section 12.1): d-> d
|}];;
