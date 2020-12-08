type edge = int * int * int * int
type graph = (edge list) Array.t
type t =
  | MaxFlow of graph

let mk_max_flow ~size = MaxFlow (Array.make size [])

let add_edge ~src ~dest ~cap = function MaxFlow g ->
  if src != dest then
    g.(src) <- (dest, cap, 0, List.length g.(dest)) :: g.(src)

let edges_of v = function MaxFlow g -> g.(v)

let size_of = function MaxFlow g -> Array.length g

(* TODO *)
(* let max_flow ~s ~t = function MaxFlow g -> *)
