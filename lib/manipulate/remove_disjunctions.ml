module Print = Print_syntax
module Fixpoint = Hflmc2_syntax.Fixpoint
module Formula = Hflmc2_syntax.Formula

open Hflz_typecheck
open Hflz

let tmp_var_name = "k"

let id_gen () =
  let id = Id.gen_id () in
  {Id.id=id; name=tmp_var_name ^ string_of_int id; ty=Type.TySigma (Type.TyBool ())}

let as_var v = {v with Id.ty=Type.TyBool ()}

let rec convert_argty argty =
  match argty with
  | Type.TyInt -> Type.TyInt
  | Type.TySigma ty -> Type.TySigma (convert_ty ty)
and convert_ty ty =
  match ty with
  | Type.TyBool () -> Type.TyArrow (id_gen (), TyBool ())
  | Type.TyArrow (id, ty2) ->
    Type.TyArrow (
      {id with ty = convert_argty id.ty},
      convert_ty ty2
    )

let convert_formula env phi =
  let rec go env phi = match phi with
    | Bool true -> Abs (id_gen (), Bool true)
    | Bool false ->
      let id = id_gen () in
      Abs (id, Var (as_var id))
    | Pred (op, as') ->
      let id = id_gen () in
      Abs (id, Or (Pred (op, as'), Var (as_var id)))
    | Or (p1, p2) ->
      let id = id_gen () in
      Abs (id, App (go env p1, App (go env p2, Var (as_var id))))
    | And (p1, p2) ->
      let id = id_gen () in
      Abs (id,
        And (
          App (go env p1, Var (as_var id)),
          App (go env p2, Var (as_var id))
        ))
    | Forall (x, p) ->
      let id = id_gen () in
      Abs (id,
        Forall (x, App (go env p, Var (as_var id)))
      )
    | App (p1, Arith e) ->
      App (go env p1, Arith e)
    | App (p1, p2) ->
      App (go env p1, go env p2)
    | Abs _ -> begin
      let rec g env p2 = match p2 with
        | Abs (x, p2') ->
          let x = {x with ty=convert_argty x.ty} in
          let env = match x.ty with | TyInt -> env | TySigma ty -> ({x with ty}::env) in
          Abs (x, g env p2')
        | _ ->
          let id = id_gen () in
          Abs (id, App (go env p2, Var (as_var id)))
      in
      g env phi
    end
    | Var x -> begin
      match List.find_all (fun x' -> Id.eq x x') env with
      | [x'] -> Var x'
      | _ -> assert false
    end
    | Exists _ -> assert false
    | Arith _ -> assert false
  in
  go env phi    
  
let convert hes =
  let (entry, rules) = hes in
  let rules = List.map (fun ({var; _} as rule) -> {rule with var = {var with ty = convert_ty var.ty}}) rules in
  let env = List.map (fun {var; _} -> var) rules in
  let rules =
    List.map
      (fun {var; body; fix} ->
        let _, body =
          convert_formula env body
          |> (Hflz_util.beta Hflmc2_syntax.IdMap.empty) in
        {var; body; fix}
      )
      rules
  in
  let _, entry =
    convert_formula env entry
    |> (Hflz_util.beta Hflmc2_syntax.IdMap.empty) in
  let hes = (App (entry, Bool false), rules) in
  type_check hes;
  hes
