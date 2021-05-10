open Hflmc2_syntax
open Hflz

val add_arguments : unit Type.ty t * unit Type.ty hes_rule list ->
int -> int -> bool -> (unit Type.ty t * unit Type.ty hes_rule list) * (unit Id.t, Hflz_util.variable_type, IdMap.Key.comparator_witness) Base.Map.t
val show_id_map : (unit Id.t, 'a, IdMap.Key.comparator_witness) Base.Map.t -> ('a -> string) -> string
