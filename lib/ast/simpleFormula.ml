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

let mk_and fmls = AndNode fmls
let mk_or fmls = OrNode fmls
let mk_forall bounds fml = ForallNode (bounds, fml)
let mk_exists bounds fml = ExistsNode (bounds, fml)
let mk_top () = TopNode ()
let mk_bot () = BotNode ()
let mk_cond psym args = CondNode (psym, args)
let mk_app pvar args = AppNode (pvar, args)

let mk_branch binop fmls =
  match binop with
  | Formula.And -> mk_and fmls
  | Formula.Or -> mk_or fmls
  | _ -> failwith @@ "SimpleFormula.mk_binop: invalid binop"

let mk_bind binder bounds fml =
  match binder with
  | Formula.Forall -> mk_forall bounds fml
  | Formula.Exists -> mk_exists bounds fml

let is_and = function AndNode _ -> true | _ -> false
let is_or = function OrNode _ -> true | _ -> false
let is_forall = function ForallNode _ -> true | _ -> false
let is_exists = function ExistsNode _ -> true | _ -> false
let is_top = function TopNode _ -> true | _ -> false
let is_bot = function BotNode _ -> true | _ -> false
let is_cond = function CondNode _ -> true | _ -> false
let is_app = function AppNode _ -> true | _ -> false

let is_branch = function AndNode _ | OrNode _ -> true | _ -> false
let is_bind = function ForallNode _ | ExistsNode _ -> true | _ -> false
let is_atom = function TopNode _ | BotNode _ | CondNode _ | AppNode _ -> true | _ -> false

let let_and = function AndNode fmls -> fmls | _ -> assert false
let let_or = function OrNode fmls -> fmls | _ -> assert false
let let_forall = function ForallNode (bounds, fml) -> bounds, fml | _ -> assert false
let let_exists = function ExistsNode (bounds, fml) -> bounds, fml | _ -> assert false
let let_cond = function CondNode (psym, args) -> psym, args | _ -> assert false
let let_app = function AppNode (pvar, args) -> pvar, args | _ -> assert false

let is_certain_branch op = function
  | AndNode _ -> op = Formula.And
  | OrNode _ -> op = Formula.Or
  | _ -> false

let let_branch = function
  | AndNode fmls -> Formula.And, fmls
  | OrNode fmls -> Formula.Or, fmls
  | _ -> assert false

let let_bind = function
  | ForallNode (args, fml) -> Formula.Forall, args, fml
  | ExistsNode (args, fml) -> Formula.Exists, args, fml
  | _ -> assert false

let fst (x, _) = x

let rec get_ftv = function
  | AndNode fmls | OrNode fmls ->
    List.map get_ftv fmls
    |> List.fold_left Core.Set.Poly.union Core.Set.Poly.empty
  | ForallNode (bounds, fml) | ExistsNode (bounds, fml) ->
    Core.Set.Poly.diff (get_ftv fml) (List.map fst bounds |> Core.Set.Poly.of_list)
  | CondNode (_, args) | AppNode (_, args) ->
    List.map Term.get_ftv args
    |> List.fold_left Core.Set.Poly.union Core.Set.Poly.empty
  | TopNode () | BotNode () ->
    Core.Set.Poly.empty

let rec get_fpv = function
  | AndNode fmls | OrNode fmls ->
    List.map get_fpv fmls
    |> List.fold_left Core.Set.Poly.union Core.Set.Poly.empty
  | ForallNode (_, fml) | ExistsNode (_, fml) ->
    get_fpv fml
  | AppNode (pvar, _) -> Core.Set.Poly.of_list [pvar]
  | CondNode _ | TopNode () | BotNode () ->
    Core.Set.Poly.empty

let mk_branch_with_simplification_one op fmls =
  let f = match op with Formula.And -> is_top | Formula.Or -> is_bot | _ -> assert false in
  let fmls = List.filter (fun fml -> f fml |> not) fmls in
  if List.exists (match op with Formula.And -> is_bot | Formula.Or -> is_top | _ -> assert false) fmls then
    match op with Formula.And -> BotNode () | Formula.Or -> TopNode () | _ -> assert false
  else
    match fmls with
    | [] -> (match op with Formula.And -> TopNode () | Formula.Or -> BotNode () | _ -> assert false)
    | [fml] -> fml
    | fmls ->
      List.fold_left
        (fun fmls fml ->
           if is_certain_branch op fml then
             let _, fmls' = let_branch fml in
             List.rev_append fmls' fmls
           else
             fml :: fmls
        )
        []
        fmls
      |> List.rev
      |> mk_branch op

let mk_bind_with_filter binder bounds fml =
  let ftv = get_ftv fml in
  let bounds = List.filter (fun (tvar, _) -> Core.Set.Poly.mem ftv tvar) bounds in
  mk_bind binder bounds fml

(*
  (a: int, b: int) @ (a: bool, c: int) -> (a: bool, b: int, c: int)
*)
let update_bounds bounds bounds' =
  let ht = Hashtbl.create 1234 in
  List.iter
    (fun (tvar, sort) -> Hashtbl.add ht tvar sort)
    (bounds @ bounds');
  Hashtbl.to_seq ht |> List.of_seq

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
let rec simplify formula =
  match formula with
  | ForallNode _
  | ExistsNode _ ->
    let binder, bounds, fml = let_bind formula in
    let fml = simplify fml in
    if is_bind fml then
      let binder', bounds', fml' = let_bind fml in
      if binder = binder' then
        mk_bind binder (update_bounds bounds bounds') fml'
      else
        mk_bind binder bounds fml
    else
      mk_bind binder bounds fml
  | AndNode fmls ->
    let fmls = List.map simplify fmls in
    if List.exists is_bot fmls then
      mk_bot ()
    else
      let fmls = List.filter (fun fml -> is_top fml |> not) fmls in
      (
        match fmls with
        | [] -> mk_top ()
        | [fml] -> fml
        | _ -> mk_branch_with_simplification_one Formula.And fmls
      )
  | OrNode fmls ->
    let fmls = List.map simplify fmls in
    if List.exists is_top fmls then
      mk_top ()
    else
      let fmls = List.filter (fun fml -> is_bot fml |> not) fmls in
      (
        match fmls with
        | [] -> mk_bot ()
        | [fml] -> fml
        | _ -> mk_branch_with_simplification_one Formula.Or fmls
      )
  | AppNode _
  | CondNode _
  | TopNode ()
  | BotNode () ->
    formula

let of_atom atom =
  if Atom.is_true atom then
    mk_top ()
  else if Atom.is_false atom then
    mk_bot ()
  else if Atom.is_symapp atom then
    let psym, args, _ = Atom.let_symapp atom in
    mk_cond psym args
  else if Atom.is_varapp atom then
    let pvar, args, _ = Atom.let_varapp atom in
    mk_app pvar args
  else
    failwith @@ Printf.sprintf "SimpleFormula.of_atom: unsupported atom"

let rec of_formula_rep fml =
  if Formula.is_binop fml then
    let binop, fml1, fml2, _ = Formula.let_binop fml in
    let fml1 = of_formula_rep fml1 in
    let fml2 = of_formula_rep fml2 in
    mk_branch binop [fml1; fml2]
  else if Formula.is_bind fml then
    let binder, bounds, fml, _ = Formula.let_bind fml in
    let fml = of_formula_rep fml in
    mk_bind binder bounds fml
  else if Formula.is_atom fml then
    let atom, _ = Formula.let_atom fml in
    of_atom atom
  else
    failwith @@ Printf.sprintf "SimpleFormula.of_formula_rep: unsupported formula"

let of_formula fml =
  of_formula_rep fml |> simplify

let rec formula_of fml =
  match fml with
  | AndNode fmls ->
    Formula.and_of (List.map formula_of fmls) Dummy
  | OrNode fmls ->
    Formula.or_of (List.map formula_of fmls) Dummy
  | ForallNode (bounds, fml) ->
    let fml = formula_of fml in
    Formula.mk_forall_if_bounded bounds fml Dummy
  | ExistsNode (bounds, fml) ->
    let fml = formula_of fml in
    Formula.mk_exists_if_bounded bounds fml Dummy
  | TopNode () ->
    let atom = Atom.mk_true Dummy in
    Formula.mk_atom atom Dummy
  | BotNode () ->
    let atom = Atom.mk_false Dummy in
    Formula.mk_atom atom Dummy
  | CondNode (psym, args) ->
    let atom = Atom.mk_app (Predicate.mk_psym psym) args Dummy in
    Formula.mk_atom atom Dummy
  | AppNode (pvar, args) ->
    let sorts = List.init (List.length args) (fun _ -> T_int.SInt) in
    let atom = Atom.mk_app (Predicate.mk_var pvar sorts) args Dummy in
    Formula.mk_atom atom Dummy

let rec neg = function
  | AndNode fmls -> OrNode (List.map neg fmls)
  | OrNode fmls -> AndNode (List.map neg fmls)
  | ForallNode (bounds, fml) -> ExistsNode (bounds, neg fml)
  | ExistsNode (bounds, fml) -> ForallNode (bounds, neg fml)
  | TopNode () -> BotNode ()
  | BotNode () -> TopNode ()
  | CondNode (psym, args) ->
    let psym = Predicate.simplify_neg (Predicate.mk_psym psym) |> Predicate.let_psym in
    CondNode (psym, args)
  | AppNode _ -> raise (Invalid_argument "pvar is included")
