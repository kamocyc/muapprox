open Hflmc2_syntax

type 'a t

val lookup : 'b Id.t -> 'a t -> 'a Id.t
val update : 'a Id.t list -> 'a t -> 'a t
val create : 'a Id.t list -> 'a t
val remove : 'a Id.t list -> 'a t -> 'a t
val merge : 'a t list -> 'a t
val to_list : 'a t -> 'a Id.t list