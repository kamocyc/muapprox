type tag_ = TagUse | TagNotUse

type funty =
  | Prop
  | Fun of argty * funty
and argty =
  | Int
  | Argty of funty * tag_

type afunty =
  | AProp
  | AFun of aargty * afunty
and aargty =
  | AAIntPair of afunty
  | AAFun of afunty
  | AAInt

let rec conv_argty ty =
  match ty with
  | Int -> AAInt
  | Argty (ty, TagUse) ->
    AAIntPair (conv_funty ty)
  | Argty (ty, TagNotUse) ->
    AAFun (conv_funty ty)
and conv_funty ty =
  match ty with
  | Prop -> AProp
  | Fun (argty, ty2) ->
    AFun (
      conv_argty argty,
      conv_funty ty2)
    

type id = string

type arith =
  Int of int | Var of id | Op of arith * arith

type tagged_hflz =
  Tagged of hflz
and hflz =
  | Ge of arith * arith
  | Or of hflz * hflz
  | And of hflz * hflz
  | Abs of id * hflz
  | App of hflz * tagged_hflz
  | AppInt of hflz * arith
  | Mu of id * hflz
  | Nu of id * hflz
