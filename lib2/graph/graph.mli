
type t = GRAPH of int list array

val init: int -> t
val of_edges: int -> (int * int) list -> t
val add_edge: int -> int -> t -> unit
val size: t -> int
val get_next_nids: int -> t -> int list
val reset_node: int -> t -> unit
val reverse_edges: t -> t
val reachable_nodes_from: ?start_is_reachable_initially: bool ->  int -> t -> int list
val string_of_graph: t -> string
