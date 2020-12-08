
type t = GRAPH of int list array

let init sz = GRAPH (Array.init sz (fun _ -> []))
let add_edge from_nid to_nid = function GRAPH graph ->
  graph.(from_nid) <- (to_nid :: graph.(from_nid))

let of_edges sz edges =
  let graph = init sz in
  List.iter
    (fun (from_nid, to_nid) ->
       add_edge from_nid to_nid graph
    )
    edges;
  graph

let size = function GRAPH graph ->
  Array.length graph

let get_next_nids nid = function GRAPH graph ->
  graph.(nid)

let reset_node nid = function GRAPH graph ->
  for i = 0 to Array.length graph - 1 do
    graph.(i) <-
      if i = nid then
        []
      else
        List.filter
          (fun to_nid -> to_nid <> nid)
          graph.(i)
  done

let reverse_edges = function GRAPH graph ->
  let new_graph = init (Array.length graph) in
  Array.iteri
    (fun nid to_list ->
       List.iter
         (fun to_nid -> add_edge to_nid nid new_graph)
         to_list
    )
    graph;
  new_graph

let reachable_nodes_from ?(start_is_reachable_initially = true) start_nid = function GRAPH graph ->
  let queue = Queue.create () in
  let used = Array.init (Array.length graph) (fun _ -> false) in
  if start_is_reachable_initially then
    used.(start_nid) <- true;
  Queue.push start_nid queue;
  while not (Queue.is_empty queue) do
    let nid = Queue.pop queue in
    List.iter
      (fun to_nid ->
         if not used.(to_nid) then (
           used.(to_nid) <- true;
           Queue.push to_nid queue
         )
      )
      graph.(nid)
  done;
  List.init (Array.length graph) (fun i -> i)
  |> List.filter (fun i -> used.(i))

let string_of_graph = function GRAPH graph ->
  Array.mapi
    (fun nid to_nids ->
       Printf.sprintf "%s: %s"
         (string_of_int nid)
         (
           List.map string_of_int to_nids
           |> String.concat ", "
         )
    )
    graph
  |> Array.to_list
  |> String.concat "\n"
