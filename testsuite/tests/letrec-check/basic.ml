(* TEST
 expect;
*)

let rec x = (x; ());;
[%%expect{|
val x : unit = ()
|}];;

let rec x = "x";;
[%%expect{|
val x : string = "x"
|}];;

let rec x = let x = () in x;;
[%%expect{|
val x : unit = ()
|}];;

let rec x = let y = (x; ()) in y;;
[%%expect{|
val x : unit = ()
|}];;

let rec x = let y = () in x;;
[%%expect{|
Line 1, characters 0-27:
1 | let rec x = let y = () in x;;
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The following recursive definitions form a cycle of
       non-statically constructive values (see manual section 12.1): x-> x
|}];;

let rec x = [y]
and y = let x = () in x;;
[%%expect{|
val y : unit = ()
val x : unit list = [()]
|}];;

let rec x = [y]
and y = let rec x = () in x;;
[%%expect{|
val y : unit = ()
val x : unit list = [()]
|}];;

let rec x =
  let a = x in
  fun () -> a ()
and y =
  [x];;
[%%expect{|
val x : unit -> 'a = <fun>
val y : (unit -> 'a) list = [<fun>]
|}];;

let rec x = [|y|] and y = 0;;
[%%expect{|
val y : int = 0
val x : int array = [|0|]
|}];;


let rec x = (y, y)
and y = fun () -> ignore x;;
[%%expect{|
val y : unit -> unit = <fun>
val x : (unit -> unit) * (unit -> unit) = (<fun>, <fun>)
|}];;

let rec x = Some y
and y = fun () -> ignore x
;;
[%%expect{|
val y : unit -> unit = <fun>
val x : (unit -> unit) option = Some <fun>
|}];;

let rec x = ignore x;;
[%%expect{|
Line 1, characters 0-20:
1 | let rec x = ignore x;;
    ^^^^^^^^^^^^^^^^^^^^
Error: The following recursive definitions form a cycle of
       non-statically constructive values (see manual section 12.1): x-> x
|}];;

let rec x = y 0 and y _ = ();;
[%%expect{|
val y : int -> unit = <fun>
val x : unit = ()
|}];;

let rec b = if b then true else false;;
[%%expect{|
Line 1, characters 0-37:
1 | let rec b = if b then true else false;;
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The following recursive definitions form a cycle of
       non-statically constructive values (see manual section 12.1): b-> b
|}];;

let rec x = function
    Some _ -> ignore (y [])
  | None -> ignore (y [])
and y = function
    [] -> ignore (x None)
  | _ :: _ -> ignore (x None)
    ;;
[%%expect{|
val x : 'a option -> unit = <fun>
val y : 'a list -> unit = <fun>
|}];;

(* used to be accepted, see PR#7696 *)
let rec x = { x with contents = 3 }  [@ocaml.warning "-23"];;
[%%expect{|
Line 1, characters 0-59:
1 | let rec x = { x with contents = 3 }  [@ocaml.warning "-23"];;
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The following recursive definitions form a cycle of
       non-statically constructive values (see manual section 12.1): x-> x
|}];;

(* this is rejected as `c` will be dereferenced during the copy,
   and is not yet fully defined *)
let rec c = { c with Complex.re = 1.0 };;
[%%expect{|
Line 1, characters 0-39:
1 | let rec c = { c with Complex.re = 1.0 };;
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The following recursive definitions form a cycle of
       non-statically constructive values (see manual section 12.1): c-> c
|}];;

let rec x = `A y
and y = fun () -> ignore x
;;
[%%expect{|
val y : unit -> unit = <fun>
val x : [> `A of unit -> unit ] = `A <fun>
|}];;

let rec x = { contents = y }
and y = fun () -> ignore x;;
[%%expect{|
val x : (unit -> unit) ref = {contents = <fun>}
val y : unit -> unit = <fun>
|}];;

let r = ref (fun () -> ())
let rec x = fun () -> r := x;;
[%%expect{|
val r : (unit -> unit) ref = {contents = <fun>}
val x : unit -> unit = <fun>
|}];;

let rec x = fun () -> y.contents and y = { contents = 3 };;
[%%expect{|
val x : unit -> int = <fun>
val y : int ref = {contents = 3}
|}];;

let r = ref ()
let rec x = r := x;;
[%%expect{|
val r : unit ref = {contents = ()}
Line 2, characters 0-18:
2 | let rec x = r := x;;
    ^^^^^^^^^^^^^^^^^^
Error: The following recursive definitions form a cycle of
       non-statically constructive values (see manual section 12.1): x-> x
|}];;

let rec x =
  for i = 0 to 1 do
    let z = y in ignore z
  done
and y = x; ();;
[%%expect{|
Line 5, characters 0-13:
5 | and y = x; ();;
    ^^^^^^^^^^^^^
Error: The following recursive definitions form a cycle of
       non-statically constructive values (see manual section 12.1):
       x-> y-> x-> y
|}];;

let rec x =
  for i = 0 to y do
    ()
  done
and y = 10;;
[%%expect{|
val y : int = 10
val x : unit = ()
|}];;

let rec x =
  for i = y to 10 do
    ()
  done
and y = 0;;
[%%expect{|
val y : int = 0
val x : unit = ()
|}];;

let rec x =
  while false do
    let y = x in ignore y
  done
and y = x; ();;
[%%expect{|
Lines 1-4, characters 0-6:
1 | let rec x =
2 |   while false do
3 |     let y = x in ignore y
4 |   done
Error: The following recursive definitions form a cycle of
       non-statically constructive values (see manual section 12.1): x-> x
|}];;

let rec x =
  while y do
    ()
  done
and y = false;;
[%%expect{|
val y : bool = false
val x : unit = ()
|}];;

let rec x =
  while y do
    let y = x in ignore y
  done
and y = false;;
[%%expect{|
Lines 1-4, characters 0-6:
1 | let rec x =
2 |   while y do
3 |     let y = x in ignore y
4 |   done
Error: The following recursive definitions form a cycle of
       non-statically constructive values (see manual section 12.1): x-> x
|}];;



let rec x = y.contents and y = { contents = 3 };;
[%%expect{|
val y : int ref = {contents = 3}
val x : int = 3
|}];;

let rec x = assert y and y = true;;
[%%expect{|
val y : bool = true
val x : unit = ()
|}];;

(* Recursively constructing arrays of known non-float type is permitted *)
let rec deep_cycle : [`Tuple of [`Shared of 'a] array] as 'a
  = `Tuple [| `Shared deep_cycle |];;
[%%expect{|
val deep_cycle : [ `Tuple of [ `Shared of 'a ] array ] as 'a =
  `Tuple [|`Shared <cycle>|]
|}];;

(* Constructing float arrays was disallowed altogether at one point
   by an overzealous check.  Constructing float arrays in recursive
   bindings is fine when they don't partake in the recursion. *)
let rec _x = let _ = [| 1.0 |] in 1. in ();;
[%%expect{|
- : unit = ()
|}];;

(* The builtin Stdlib.ref is currently treated as a constructor.
   Other functions of the same name should not be so treated. *)
let _ =
  let module Stdlib =
  struct
    let ref _ = assert false
  end in
  let rec x = Stdlib.ref y
  and y = fun () -> ignore x
  in (x, y)
;;
[%%expect{|
Line 6, characters 2-26:
6 |   let rec x = Stdlib.ref y
      ^^^^^^^^^^^^^^^^^^^^^^^^
Error: The following recursive definitions form a cycle of
       non-statically constructive values (see manual section 12.1):
       x-> y-> x
|}];;

(* An example, from Leo White, of let rec bindings that allocate
   values of unknown size *)
let foo p x =
  let rec f =
    if p then (fun y -> x + g y) else (fun y -> g y)
  and g =
    if not p then (fun y -> x - f y) else (fun y -> f y)
  in
  (f, g)
;;
[%%expect{|
Lines 4-5, characters 2-56:
4 | ..and g =
5 |     if not p then (fun y -> x - f y) else (fun y -> f y)
Error: The following recursive definitions form a cycle of
       non-statically constructive values (see manual section 12.1):
       g-> f-> g
|}];;

let rec x =
  match let _ = y in raise Not_found with
    _ -> "x"
  | exception Not_found -> "z"
and y = match x with
  z -> ("y", z);;
[%%expect{|
Lines 5-6, characters 0-15:
5 | and y = match x with
6 |   z -> ("y", z)..
Error: The following recursive definitions form a cycle of
       non-statically constructive values (see manual section 12.1):
       y-> x-> y
|}];;


(* To compute the dependencies of mutually-recursive bindings,
   transitive dependencies must be taken into account.

   The example below was causing a segfault in 4.08+dev.
*)
let rec wrong =
  (* x depends on y,
     and y depends on wrong,
     so it is important to notice that x transitively depends on wrong;

     an earlier version of our letrec analysis would only report that
     y depends on wrong, which seems safe as y is not used in the
     body.
  *)
  let rec x = ref y
  and y = ref wrong
  in ref ("foo" ^ ! ! !x);;
[%%expect{|
Lines 1-12, characters 0-25:
 1 | let rec wrong =
 2 |   (* x depends on y,
 3 |      and y depends on wrong,
 4 |      so it is important to notice that x transitively depends on wrong;
 5 |
...
 9 |   *)
10 |   let rec x = ref y
11 |   and y = ref wrong
12 |   in ref ("foo" ^ ! ! !x)..
Error: The following recursive definitions form a cycle of
       non-statically constructive values (see manual section 12.1):
       wrong-> wrong
|}]

(* in this case, x does not depend on y, so everything is fine *)
let rec okay =
  let rec x = ref "bar"
  and _y = ref okay in
  ref ("foo" ^ ! x);;
[%%expect{|
val okay : string ref = {contents = "foobar"}
|}]
