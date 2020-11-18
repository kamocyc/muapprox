module Hflz = Hflmc2_syntax.Hflz
module Id = Hflmc2_syntax.Id
module Formula = Hflmc2_syntax.Formula
open Hflz
open Hflmc2_syntax.Print

let id : 'ty Id.t t =
  fun ppf x -> Fmt.pf ppf "%s" (Id.to_string x)
let simple_ty_ = simple_ty_
let simple_ty = simple_ty
(* Hflz *)

let rec hflz_ : (Prec.t -> 'ty Fmt.t) -> Prec.t -> 'ty Hflz.t Fmt.t =
  fun format_ty_ prec ppf (phi : 'ty Hflz.t) -> match phi with
    | Bool true -> Fmt.string ppf "true"
    | Bool false -> Fmt.string ppf "false"
    | Var x -> Fmt.pf ppf "(%a :%a)" id x (format_ty_ Prec.zero) x.ty
    | Or(phi1,phi2)  ->
        show_paren (prec > Prec.or_) ppf "@[<hv 0>%a@ || %a@]"
          (hflz_ format_ty_ Prec.or_) phi1
          (hflz_ format_ty_ Prec.or_) phi2
    | And (phi1,phi2)  ->
        show_paren (prec > Prec.and_) ppf "@[<hv 0>%a@ && %a@]"
          (hflz_ format_ty_ Prec.and_) phi1
          (hflz_ format_ty_ Prec.and_) phi2
    | Abs (x, psi) ->
        show_paren (prec > Prec.abs) ppf "@[<1>λ%a:%a.@,%a@]"
          id x
          (argty (format_ty_ Prec.(succ arrow))) x.ty
          (hflz_ format_ty_ Prec.abs) psi
    | Forall (x, psi) ->
        show_paren (prec > Prec.abs) ppf "@[<1>∀%a.@,%a@]"
          id x
          (hflz_ format_ty_ Prec.abs) psi
    | Exists (x, psi) ->
        show_paren (prec > Prec.abs) ppf "@[<1>∃%a.@,%a@]"
          id x
          (hflz_ format_ty_ Prec.abs) psi
    | App (psi1, psi2) ->
        show_paren (prec > Prec.app) ppf "@[<1>%a@ %a@]"
          (hflz_ format_ty_ Prec.app) psi1
          (hflz_ format_ty_ Prec.(succ app)) psi2
    | Arith a -> arith_ prec ppf a
    | Pred (pred, as') ->
        show_paren (prec > Prec.eq) ppf "%a"
          formula (Formula.Pred(pred, as'))

let hflz : (Prec.t -> 'ty Fmt.t) -> 'ty Hflz.t Fmt.t =
  fun format_ty_ -> hflz_ format_ty_ Prec.zero

let hflz_hes_rule : (Prec.t -> 'ty Fmt.t) -> 'ty Hflz.hes_rule Fmt.t =
  fun format_ty_ ppf rule ->
    Fmt.pf ppf "@[<2>%s : %a =%a@ %a@]"
      (Id.to_string rule.var)
      (format_ty_ Prec.zero) rule.var.ty
      fixpoint rule.fix
      (hflz format_ty_) rule.body

let hflz_hes : (Prec.t -> 'ty Fmt.t) -> 'ty Hflz.hes Fmt.t =
  fun format_ty_ ppf hes ->
    Fmt.pf ppf "@[<v>%a@]"
      (Fmt.list (hflz_hes_rule format_ty_)) hes

module MachineReadable = struct  
    
  let replace_apos s =
    s
    |> Str.global_replace (Str.regexp "'") "_ap_"
    |> Str.global_replace (Str.regexp "!") "_exc_"
    
  let id' : 'ty Id.t t =
    fun ppf x -> Fmt.pf ppf "%s" (replace_apos @@ Id.to_string x)
  
  let id_' = fun prec ppf x -> Fmt.pf ppf "%s" (replace_apos @@ Id.to_string x)
  
  let arith_  =
    fun prec ppf a -> gen_arith_ id_' prec ppf a
  
  let formula_ : Formula.t t_with_prec =
    gen_formula_ void_ id_'
  let formula : Formula.t Fmt.t =
    formula_ Prec.zero
    
  let rec hflz_' : (Prec.t -> 'ty Fmt.t) -> Prec.t -> 'ty Hflz.t Fmt.t =
    fun format_ty_ prec ppf (phi : 'ty Hflz.t) -> match phi with
      | Bool true -> Fmt.string ppf "true"
      | Bool false -> Fmt.string ppf "false"
      | Var x -> id' ppf x
      | Or(phi1,phi2)  ->
          show_paren (prec > Prec.or_) ppf "@[<hv 0>%a@ || %a@]"
            (hflz_' format_ty_ Prec.or_) phi1
            (hflz_' format_ty_ Prec.or_) phi2
      | And (phi1,phi2)  ->
          show_paren (prec > Prec.and_) ppf "@[<hv 0>%a@ && %a@]"
            (hflz_' format_ty_ Prec.and_) phi1
            (hflz_' format_ty_ Prec.and_) phi2
      | Abs (x, psi) -> failwith @@ "(Print.Hflz) Abstractions should be converted to HES equations."
      | Forall (x, psi) ->
          (* TODO: ∀は出力したほうがいい？ => 付けるべき。付けないとなぜか\がつくことがある *)
          show_paren (prec > Prec.abs) ppf "@[<1>∀%a.@,%a@]"
            id' x
            (* (argty (format_ty_ Prec.(succ arrow))) x.ty *)
            (hflz_' format_ty_ Prec.abs) psi
      | Exists (x, psi) -> 
        show_paren (prec > Prec.abs) ppf "@[<1>∃%a.@,%a@]"
            id' x
            (* (argty (format_ty_ Prec.(succ arrow))) x.ty *)
            (hflz_' format_ty_ Prec.abs) psi
      | App (psi1, psi2) ->
          show_paren (prec > Prec.app) ppf "@[<1>%a@ %a@]"
            (hflz_' format_ty_ Prec.app) psi1
            (hflz_' format_ty_ Prec.(succ app)) psi2
      | Arith a ->
          arith_ prec ppf a
      | Pred (pred, as') ->
          show_paren (prec > Prec.eq) ppf "%a"
            formula (Formula.Pred(pred, as'))

  let fprint_space f () = fprintf f " "

  let hflz' : (Prec.t -> 'ty Fmt.t) -> 'ty Hflz.t Fmt.t =
    fun format_ty_ -> hflz_' format_ty_ Prec.zero
  
  let hflz_hes_rule' : (Prec.t -> 'ty Fmt.t) -> 'ty Hflz.hes_rule Fmt.t =
    fun format_ty_ ppf rule ->
      let args, phi = Hflz.decompose_abs rule.body in
      (* 'ty Type.arg Id.t を表示したい *)
      Fmt.pf ppf "@[<2>%s %a =%a@ %a.@]"
        (Id.to_string rule.var)
        (pp_print_list ~pp_sep:fprint_space id') args
        (* (format_ty_ Prec.zero) rule.var.ty *)
        fixpoint rule.fix
        (hflz' format_ty_) phi
  
  let hflz_hes' : (Prec.t -> 'ty Fmt.t) -> 'ty Hflz.hes Fmt.t =
    fun format_ty_ ppf hes ->
      Fmt.pf ppf "@[<v>%a@]"
        (Fmt.list (hflz_hes_rule' format_ty_)) hes
end
