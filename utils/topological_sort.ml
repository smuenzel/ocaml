

type 'a edge = { from : 'a; to_: 'a; }

type 'a result = Cycle of 'a list | Sorted of 'a list

type state = Unvisited | Visited | Visiting

module Int_map = Map.Make(Int)

let sort
    (type n)
    ?(compare_node = (compare : n -> n -> int))
    (nodes : n list)
    (edges : n edge list)
  =
  let module M = Map.Make(struct type t = n let compare = compare_node end) in
  let _, node_to_id, id_to_node =
    List.fold_left
      (fun (idx, to_id, to_node) node ->
         idx + 1, M.add node idx to_id, Int_map.add idx node to_node
      )
      (0, M.empty, Int_map.empty)
      nodes
  in
  let edges =
    List.fold_left
      (fun edges { from; to_ } ->
         Int_map.add_to_list (M.find from node_to_id) (M.find to_ node_to_id) edges
      )
      Int_map.empty
      edges
  in
  let states = Array.init (List.length nodes) (fun _ -> Unvisited) in
  let sorted = ref [] in
  let exception Has_cycle of int list in
  let rec visit path node =
    match states.(node) with
    | Visiting -> raise (Has_cycle (node::path))
    | Visited -> ()
    | Unvisited ->
        states.(node) <- Visiting;
        let path = node::path in
        begin match Int_map.find_opt node edges with
        | None -> ()
        | Some edges -> List.iter (visit path) edges
        end;
        states.(node) <- Visited;
        sorted := node::!sorted;
        ()
  in
  try
    Int_map.iter (fun node _ -> visit [] node) edges;
    Sorted (List.rev_map (fun id -> Int_map.find id id_to_node) !sorted)
  with
  | Has_cycle path -> Cycle (List.rev_map (fun id -> Int_map.find id id_to_node) path)

