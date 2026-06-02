(* TEST
 expect;
*)

(* Example from Eduardo Souza *)
module type S = sig type t type e val v : e -> t end
let helper (type a) (module M : S with type t = a) _ : a = assert false
let outer (type a) (type b) (module M : S with type e = a and type t = b) e =
  helper (module M) (M.v e)

[%%expect{|
module type S = sig type t type e val v : e -> t end
val helper : (module S with type t = 'a) -> 'b -> 'a = <fun>
Uncaught exception: Ctype.Unify(_)

|}]
