
module String_set = Misc.Stdlib.String.Set

type mode =
  | Ignore
  | Delay of t
  | Guard of guard
  | Return
  | Dereference
  | Project of String_set.t
  | Apply
and guard =
  | Variant_constructor
  | Record of String_set.t


let rec compose outer inner =
  match outer, inner with
  | Ignore, _ -> Ignore
  | _, Ignore -> Ignore
  | Dereference, _ -> Dereference
  | Delay out_delay, inner -> Delay (compose out_delay inner)
  | Guard _, Return -> outer
  | Project id, Guard (Record id') when not (String_set.disjoint id id') -> Return


(**)
