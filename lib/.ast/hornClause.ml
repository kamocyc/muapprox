open Core
open Logic

type t = (Formula.t * Atom.t) list

let add_goal hc phi = (phi, Atom.mk_false Dummy) :: hc
let add_definite hc phi atom = (phi, atom) :: hc

let formula_of = function
  | [] -> Formula.mk_atom (Atom.mk_true Dummy) Dummy
  | (body, head) :: xs ->
    List.fold_left xs
      ~init:(Formula.mk_imply body (Formula.mk_atom head Dummy) Dummy)
      ~f:(fun acc (body, head) ->
          Formula.mk_and
            acc
            (Formula.mk_imply body (Formula.mk_atom head Dummy) Dummy)
            Dummy)

let decompose_conj phi = let open Formula in
  let rec aux acc = function
    | BinaryOp (And, phi1, phi2, _) ->
      aux (phi1 :: acc) phi2
    | x -> (*[x]*) x::acc
  in
  aux [] phi

let rec has_fixpoint_of_formula phi = let open Formula in
  match phi with
  | Atom (atom, _) -> has_fixpoint_of_atom atom
  | UnaryOp (_, phi, _) -> has_fixpoint_of_formula phi
  | BinaryOp (_, phi1, phi2, _) ->
    (has_fixpoint_of_formula phi1) || (has_fixpoint_of_formula phi2)
  | Bind (_, _, phi, _) ->
    has_fixpoint_of_formula phi
  | LetRec _ -> true

and has_fixpoint_of_atom atom = let open Atom in
  match atom with
  | True _ | False _ -> false
  | App (pred, args, _) ->
    (has_fixpoint_of_pred pred) || (has_fixpoint_of_args args)

and has_fixpoint_of_pred pred = let open Predicate in
  match pred with
  | Var _ | Psym _-> false
  | Fixpoint _ -> true

and has_fixpoint_of_args = function
  | [] -> false
  | x :: xs ->
    (has_fixpoint_of_term x) || (has_fixpoint_of_args xs)

and has_fixpoint_of_term t = let open Term in
  match t with
  | Var _ -> false
  | FunApp (_, args, _) -> has_fixpoint_of_args args

let has_fixpoint = has_fixpoint_of_formula


let from_formula phi = let open Formula in
  if has_fixpoint phi then
    None
  else
    let phis = decompose_conj phi in
    let rec aux acc = function
      | [] -> Some(acc)
      | BinaryOp(Imply, phi, Atom(atom, _), _) :: xs ->
        let clause = (phi, atom) in
        aux (clause :: acc) xs
      | _ -> None
    in
    aux [] phis



