(* TEST
   * expect
*)

type 'a t = private [`F]

type 'a first = F : ('b#t as 'a) first

[%%expect{|
type 'a t = private [ `F ]
Line 3, characters 21-25:
3 | type 'a first = F : ('b#t as 'a) first
                         ^^^^
Alert deprecated: old syntax for polymorphic variant type
Line 3, characters 21-25:
3 | type 'a first = F : ('b#t as 'a) first
                         ^^^^
Error: The type 'b t does not expand to a polymorphic variant type
|}]

type 'a tt = [`F]

type 'a second = F : ('b#tt as 'a) second


[%%expect{|
type 'a tt = [ `F ]
Line 3, characters 22-27:
3 | type 'a second = F : ('b#tt as 'a) second
                          ^^^^^
Alert deprecated: old syntax for polymorphic variant type
type 'a second = F : 'b tt second
|}]
