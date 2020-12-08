type info = Dummy

module Formula : sig
  type unop = Neg
  type binop = And | Or

  type t =
    | True of info | False of info
    | Atom of string * info
    | UnaryOp of unop * t * info
    | BinaryOp of binop * t * t * info

  val mk_true: info -> t
  val mk_false: info -> t

  val mk_atom: string -> info -> t
  val mk_neg: t -> info -> t
  val mk_and: t -> t -> info -> t
  val mk_or: t -> t -> info -> t

  val and_of: t list -> info -> t
  val or_of: t list -> info -> t

  val subst: t -> (string * t) list -> t

  val str_of: t -> string

  val belongs_to: t -> t -> bool
  val neg_of_clause: t -> t list
  val pos_of_clause: t -> t list

  val list_of_and: t -> t list
  val list_of_or: t -> t list
  val list_of_cnf: t -> (t list * t list) list
  val name_of_atom: t -> string

  val cnf_of: t -> (string list * string list) list
  val nnf_of: t -> t

end = struct
  type unop = Neg
  type binop = And | Or

  type t =
    | True of info | False of info
    | Atom of string * info
    | UnaryOp of unop * t * info
    | BinaryOp of binop * t * t * info

  let mk_true info = True info
  let mk_false info = False info

  let mk_atom ident info = Atom (ident, info)
  let mk_neg t info = UnaryOp(Neg, t, info)
  let mk_and t1 t2 info = BinaryOp(And, t1, t2, info)
  let mk_or t1 t2 info = BinaryOp(Or, t1, t2, info)

  let and_of ts info =
    List.fold_left (fun acc t -> mk_and acc t info) (mk_true info) ts

  let or_of ts info =
    List.fold_left (fun acc t -> mk_or acc t info) (mk_false info) ts

  let rec subst formula substitution =
    match formula with
    | True _ -> True Dummy
    | False _ -> False Dummy
    | Atom (name, info) ->
      if List.mem_assoc name substitution then
        List.assoc name substitution
      else
        Atom (name, info)
    | UnaryOp(op, formula', info) ->
      UnaryOp(op, subst formula' substitution, info)
    | BinaryOp(op, formula_0, formula_1, info) ->
      BinaryOp(op, subst formula_0 substitution, subst formula_1 substitution, info)

  let rec str_of = function
    | True _ -> "True"
    | False _ -> "False"
    | Atom(id, _) -> id
    | UnaryOp(_, t, _) -> Printf.sprintf "not (%s)" (str_of t)
    | BinaryOp(And, t1, t2, _) ->
      Printf.sprintf "(%s /\\ %s)" (str_of t1) (str_of t2)
    | BinaryOp(Or, t1, t2, _) ->
      Printf.sprintf "(%s \\/ %s)" (str_of t1) (str_of t2)

  let rec belongs_to phi1 phi2 =
    if phi1 = phi2 then true
    else
      match phi2 with
      | True _ | False _ | Atom(_, _) -> false
      | UnaryOp(_, phi2', _) -> belongs_to phi1 phi2'
      | BinaryOp(_, phi', phi'', _) -> (belongs_to phi1 phi' || belongs_to phi1 phi'')

  let rec neg_of_clause = function
    | UnaryOp(Neg, Atom(id, Dummy), _) -> [Atom(id, Dummy)]
    | Atom(_, _) | True _ | False _ -> []
    | BinaryOp(Or, phi1, phi2, _) -> neg_of_clause phi1 @ neg_of_clause phi2
    | phi -> failwith @@ Printf.sprintf "The formula %s is not of clause" (str_of phi)

  let rec pos_of_clause = function
    | UnaryOp(Neg, Atom(_, _), _) | True _ | False _ -> []
    | Atom(id, Dummy) -> [Atom(id, Dummy)]
    | BinaryOp(_, phi1, phi2, _) -> pos_of_clause phi1 @ pos_of_clause phi2
    | _ -> failwith "This formula is not of clause"

  let list_of_and phi =
    let rec inner = function
      | BinaryOp(And, phi1, phi2, _) ->
        (inner phi1) @ (inner phi2)
      | phi -> [phi]
    in
    inner phi |> List.filter (function True _ -> false | _ -> true)
    |> (fun ls -> if List.exists (function False _ -> true | _ -> false) ls then [] else ls)

  let list_of_or phi =
    let rec inner = function
      | BinaryOp(Or, phi1, phi2, _) -> (inner phi1) @ (inner phi2)
      | phi -> [phi]
    in
    inner phi |> List.filter (function False _ -> false | _ -> true)
    |> (fun ls -> if List.exists (function True _ -> true | _ -> false) ls then [] else ls)

  let list_of_cnf phi =
    list_of_and phi
    |> List.map (fun disj ->
        list_of_or disj
        |> List.fold_left (fun (neg, pos) ->
            function UnaryOp (Neg, phi, _) -> (phi::neg, pos) | phi -> (neg, phi::pos)) ([], [])
      )

  let name_of_atom = function
    | Atom (name, _) -> name
    | phi -> failwith @@ Printf.sprintf "%s is not an atom" (str_of phi)

  let rec cnf_of_aux = let open Core in let open Core.Poly in function
      | UnaryOp(Neg, (True _), _) -> [[], []]
      | UnaryOp(Neg, (False _), _) -> []
      | UnaryOp(Neg, (Atom (name, _)), _) -> [[name], []]
      | BinaryOp(And, phi1, phi2, _) ->
        let cls1, cls2 = cnf_of_aux phi1, cnf_of_aux phi2 in
        let phis, cls =
          List.partition_map
            (cls1 @ cls2)
            ~f:(fun (ns, ps) -> `Snd(ns, ps))
        in
        if phis = [] then cls else ([], [])::cls
      | BinaryOp(Or, phi1, phi2, _) ->
        let cls1, cls2 = cnf_of_aux phi1, cnf_of_aux phi2 in
        List.map
          (List.cartesian_product cls1 cls2)
          ~f:(fun ((ns1, ps1), (ns2, ps2)) ->
              ns1 @ ns2,
              ps1 @ ps2
            )
      | True _ -> [] | False _ -> [[], []]
      | Atom(name, _) -> [[], [name]]
      | phi -> failwith @@ Printf.sprintf "fail @ cnf_of %s " @@ str_of phi

  let cnf_of phi =
    phi |> cnf_of_aux |> List.map (fun (ns, ps) -> ns, ps)

  let nnf_of phi =
    let rec inner = function
      | UnaryOp(Neg, (True Dummy), _) -> False Dummy
      | UnaryOp(Neg, (False Dummy), _) -> True Dummy
      | UnaryOp(Neg, UnaryOp(Neg, phi, _), _) -> inner phi
      | UnaryOp(Neg, BinaryOp(And, phi1, phi2, _), _) ->
        let phi1', phi2' = inner (UnaryOp (Neg, phi1, Dummy)), inner (UnaryOp (Neg, phi2, Dummy)) in
        BinaryOp(Or, phi1', phi2', Dummy)
      | UnaryOp(Neg, BinaryOp(Or, phi1, phi2, _), _) ->
        let phi1', phi2' = inner (UnaryOp (Neg, phi1, Dummy)), inner (UnaryOp (Neg, phi2, Dummy)) in
        BinaryOp(And, phi1', phi2', Dummy)
      | BinaryOp(And, phi1, phi2, _) -> BinaryOp(And, inner phi1, inner phi2, Dummy)
      | BinaryOp(Or, phi1, phi2, _) -> BinaryOp(Or, inner phi1, inner phi2, Dummy)
      | phi -> phi
    in inner phi

end
