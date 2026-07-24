(* TEST
   expect;
 *)

module M = struct
  class c1 = object
    method c1 = new c1
    method c2 = new c2
    method c3 = new c3
    method c4 = new c4
    method c5 = new c5
    method c6 = new c6
    method c7 = new c7
  end
  and c2 = object
    method c1 = new c2
    method c2 = new c3
    method c3 = new c4
    method c4 = new c5
    method c5 = new c6
    method c6 = new c7
    method c7 = new c1
  end
  and c3 = object
    method c1 = new c3
    method c2 = new c4
    method c3 = new c5
    method c4 = new c6
    method c5 = new c7
    method c6 = new c1
    method c7 = new c2
  end
  and c4 = object
    method c1 = new c4
    method c2 = new c5
    method c3 = new c6
    method c4 = new c7
    method c5 = new c1
    method c6 = new c2
    method c7 = new c3
  end
  and c5 = object
    method c1 = new c5
    method c2 = new c6
    method c3 = new c7
    method c4 = new c1
    method c5 = new c2
    method c6 = new c3
    method c7 = new c4
  end
  and c6 = object
    method c1 = new c6
    method c2 = new c7
    method c3 = new c1
    method c4 = new c2
    method c5 = new c3
    method c6 = new c4
    method c7 = new c5
  end
  and c7 = object
    method c1 = new c7
    method c2 = new c1
    method c3 = new c2
    method c4 = new c3
    method c5 = new c4
    method c6 = new c5
    method c7 = new c6
  end
end

let f (x : M.c1) = (x : M.c2)

let g (x : M.c1) = (x :> M.c2)

let h x = (x :> M.c2)

(* This one is already slow in principal mode
module M1 : sig class c1 : M.c2 end = M
*)

module M2 : sig type c1 = M.c2 end = M

module M3 : sig val f : unit -> M.c2 end = struct let f () = new M.c1 end

[%%expect{|
Lines 56-64, characters 2-5:
56 | ..and c7 = object
57 |     method c1 = new c7
58 |     method c2 = new c1
59 |     method c3 = new c2
60 |     method c4 = new c3
61 |     method c5 = new c4
62 |     method c6 = new c5
63 |     method c7 = new c6
64 |   end
Error: The following recursive class definitions form a cycle: c1 -> c7
Unexecuted phrases: 5 phrases did not execute due to an error
|}]
