type edge = int * int * int * int
type graph = (edge list) Array.t
type t =
  | MaxFlow of graph

val mk_max_flow: size:int -> t

val add_edge: src:int -> dest:int -> cap:int -> t -> unit

val edges_of: int -> t -> edge list

val size_of: t -> int

(* TODO *)
(* val max_flow: s:int -> t:int -> t -> int *)
