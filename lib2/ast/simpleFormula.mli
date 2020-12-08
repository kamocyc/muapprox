open Logic

type t =
  | ForallNode of (Ident.tvar * Sort.t) list * t
  | ExistsNode of (Ident.tvar * Sort.t) list * t
  | AndNode of t list
  | OrNode of t list
  | TopNode of unit
  | BotNode of unit
  | CondNode of pred_sym * Term.t list
  | AppNode of Ident.pvar * Term.t list

val update_bounds: (Ident.tvar * Sort.t) list -> (Ident.tvar * Sort.t) list -> (Ident.tvar * Sort.t) list

val mk_and: t list -> t
val mk_or: t list -> t
val mk_forall: (Ident.tvar * Sort.t) list -> t -> t
val mk_exists: (Ident.tvar * Sort.t) list -> t -> t
val mk_top: unit -> t
val mk_bot: unit -> t
val mk_cond: pred_sym -> Term.t list -> t
val mk_app: Ident.pvar -> Term.t list -> t

val mk_branch: Formula.binop -> t list -> t
val mk_bind: Formula.binder -> (Ident.tvar * Sort.t) list -> t -> t

val is_and: t -> bool
val is_or: t -> bool
val is_forall: t -> bool
val is_exists: t -> bool
val is_top: t -> bool
val is_bot: t -> bool
val is_cond: t -> bool
val is_app: t -> bool

val is_branch: t -> bool
val is_bind: t -> bool
val is_atom: t -> bool

val let_and: t -> t list
val let_or: t -> t list
val let_forall: t -> (Ident.tvar * Sort.t) list * t
val let_exists: t -> (Ident.tvar * Sort.t) list * t
val let_cond: t -> pred_sym * Term.t list
val let_app: t -> Ident.pvar * Term.t list

val let_branch: t -> Formula.binop * t list
val let_bind: t -> Formula.binder * (Ident.tvar * Sort.t) list * t

(*
  forall x, forall y -> forall x, y
  exists x, exists y -> exists x, y
  top /\ P -> P
  bot /\ P -> bot
  top \/ P -> top
  bot \/ P -> P
  (P /\ Q) /\ R -> (P /\ Q /\ R)
  (/\ [empty]) -> top
  (\/ [empty]) -> bot
*)
val simplify: t -> t
val of_formula: Formula.t -> t
val formula_of: t -> Formula.t
val get_ftv: t -> Ident.tvar Core.Set.Poly.t
val get_fpv: t -> Ident.pvar Core.Set.Poly.t

val mk_branch_with_simplification_one: Formula.binop -> t list -> t
val mk_bind_with_filter: Formula.binder -> (Ident.tvar * Sort.t) list -> t -> t

val neg: t -> t
