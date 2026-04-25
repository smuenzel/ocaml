
type 'a edge = { from : 'a; to_: 'a; }

type 'a result = Cycle of 'a list | Sorted of 'a list

val sort
  : ?compare_node:('node -> 'node -> int)
  -> 'node list
  -> 'node edge list
  -> 'node result
