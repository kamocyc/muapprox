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

let print_arg_type (arg_type : Hflmc2_syntax.Type.simple_ty Hflmc2_syntax.Type.arg) = 
  let go arg_type = match arg_type with
    | Hflmc2_syntax.Type.TyInt -> print_string "int"
    | Hflmc2_syntax.Type.TySigma ty -> simple_ty Format.std_formatter (ty);
  in
  go arg_type;
  print_endline ""
  
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

module PrintUtil = struct
  let replace_apos s =
    s
    |> Str.global_replace (Str.regexp "'") "_ap_"
    |> Str.global_replace (Str.regexp "!") "_exc_"
    |> Str.global_replace (Str.regexp "#") "_sha_"
    
  let id' : 'ty Id.t t =
    fun ppf x -> Fmt.pf ppf "%s" (replace_apos @@ Id.to_string x)
  
  let id_' = fun prec ppf x -> Fmt.pf ppf "%s" (replace_apos @@ Id.to_string x)
  
  let arith_  =
    fun prec ppf a -> gen_arith_ id_' prec ppf a
  
  let formula_ : Formula.t t_with_prec =
    gen_formula_ void_ id_'
  let formula : Formula.t Fmt.t =
    formula_ Prec.zero
    
  let fprint_space f () = fprintf f " "
end

module FptProverHes = struct
  open PrintUtil
    
  let rec gen_formula_
      :  'bvar t_with_prec
      -> 'avar t_with_prec
      -> ('bvar, 'avar) Formula.gen_t t_with_prec =
    fun bvar avar prec ppf f -> match f with
      | Var x      -> bvar prec ppf x
      | Bool true  -> Fmt.string ppf "true"
      | Bool false -> Fmt.string ppf "false"
      | Or fs ->
          let sep ppf () = Fmt.pf ppf "@ \\/ " in
          show_paren (prec > Prec.or_) ppf "@[<hv 0>%a@]"
            (list ~sep (gen_formula_ bvar avar Prec.or_)) fs
      | And fs ->
          let sep ppf () = Fmt.pf ppf "@ /\\ " in
          show_paren (prec > Prec.and_) ppf "@[<hv 0>%a@]"
            (list ~sep (gen_formula_ bvar avar Prec.and_)) fs
      | Pred(pred',[f1;f2]) ->
          Fmt.pf ppf "@[<1>%a@ %a@ %a@]"
            (gen_arith_ avar prec) f1
            pred pred'
            (gen_arith_ avar prec) f2
      | Pred _ -> assert false
  let gen_formula
      :  'bvar t_with_prec
      -> 'avar t_with_prec
      -> ('bvar, 'avar) Formula.gen_t t =
    fun bvar avar ppf f ->
      gen_formula_ bvar avar Prec.zero ppf f
  let formula_ : Formula.t t_with_prec =
    gen_formula_ void_ id_
  let formula : Formula.t Fmt.t =
    formula_ Prec.zero

  let hflz_' =
    let rec go_ (prec : Prec.t) (ppf : formatter) (phi : 'ty Hflz.t) = match phi with
      | Bool true -> Fmt.string ppf "true"
      | Bool false -> Fmt.string ppf "false"
      | Var x -> id' ppf x
      | Or(phi1,phi2)  ->
          show_paren (prec > Prec.or_) ppf "@[<hv 0>%a@ \\/ %a@]"
            (go_ Prec.or_) phi1
            (go_ Prec.or_) phi2
      | And (phi1,phi2)  ->
          show_paren (prec > Prec.and_) ppf "@[<hv 0>%a@ /\\ %a@]"
            (go_ Prec.and_) phi1
            (go_ Prec.and_) phi2
      | Abs (x, psi) -> 
          failwith @@ "(Print.Hflz) Abstractions should be converted to HES equations."
      | Forall (x, psi) ->
          show_paren (prec > Prec.abs) ppf "@[<1>forall (%a : %a).@,%a@]"
            id' x
            (argty (simple_ty_ Prec.(succ arrow))) x.ty
            (go_ Prec.abs) psi
      | Exists (x, psi) -> 
        show_paren (prec > Prec.abs) ppf "@[<1>exists (%a : %a).@,%a@]"
            id' x
            (argty (simple_ty_ Prec.(succ arrow))) x.ty
            (go_ Prec.abs) psi
      | App (psi1, psi2) ->
          show_paren (prec > Prec.app) ppf "@[<1>%a@ %a@]"
            (go_ Prec.app) psi1
            (go_ Prec.(succ app)) psi2
      | Arith a ->
          arith_ prec ppf a
      | Pred (pred, as') ->
          show_paren (prec > Prec.eq) ppf "%a"
            formula (Formula.Pred(pred, as'))
    in go_
  
  let hflz' : 'ty Hflz.t Fmt.t = hflz_' Prec.zero
  
  let fixpoint : Hflmc2_syntax.Fixpoint.t Fmt.t =
    fun ppf t -> match t with
      | Least    -> Fmt.string ppf "mu"
      | Greatest -> Fmt.string ppf "nu"
  
  let pp_print_args_with_types fmt args =
    pp_print_list
      ~pp_sep:fprint_space
      (fun fmt arg ->
        fprintf fmt "(%a : %a)"
          id' arg
          simple_argty arg.ty)
      fmt
      args
      
  let hflz_hes_rule' : 'ty Hflz.hes_rule Fmt.t =
    fun ppf rule ->
      let args, phi = Hflz.decompose_abs rule.body in
      Fmt.pf ppf "@[<2>%s %a : bool =%a@ %a;@]"
        (Id.to_string rule.var)
        pp_print_args_with_types args
        fixpoint rule.fix
        hflz' phi
  
  let hflz_hes' : 'ty Hflz.hes Fmt.t =
    fun ppf hes ->
      match hes with
      | [] -> failwith "hflz_hes': Empty hes"
      | first_rule::hes -> begin
        Fmt.pf ppf "@[<v>%a\ns.t.\n%a@]"
          hflz' first_rule.body
          (Fmt.list hflz_hes_rule') hes
      end
    
  let save_hes_to_file hes =
    Random.self_init ();
    let r = Random.int 0x10000000 in
    let file = Printf.sprintf "/tmp/%s-%d.smt2" "nuonly" r in
    let oc = open_out file in
    let fmt = Format.formatter_of_out_channel oc in
    Format.pp_set_margin fmt 1000;
    hflz_hes' fmt hes;
    Format.pp_print_flush fmt ();
    close_out oc;
    file
end


module MachineReadable = struct
  open PrintUtil
  
  let hflz_' (format_ty_ : Prec.t -> 'ty Fmt.t) (show_forall : bool)  =
    let rec go_ (prec : Prec.t) (ppf : formatter) (phi : 'ty Hflz.t) = match phi with
      | Bool true -> Fmt.string ppf "true"
      | Bool false -> Fmt.string ppf "false"
      | Var x -> id' ppf x
      | Or(phi1,phi2)  ->
          show_paren (prec > Prec.or_) ppf "@[<hv 0>%a@ || %a@]"
            (go_ Prec.or_) phi1
            (go_ Prec.or_) phi2
      | And (phi1,phi2)  ->
          show_paren (prec > Prec.and_) ppf "@[<hv 0>%a@ && %a@]"
            (go_ Prec.and_) phi1
            (go_ Prec.and_) phi2
      | Abs (x, psi) -> begin
        show_paren (prec > Prec.abs) ppf "@[<1>\\%a.@,%a@]"
            id' x
            (* (argty (Prec.(succ arrow))) x.ty *)
            (go_ Prec.abs) psi
      end 
      (* failwith @@ "(Print.Hflz) Abstractions should be converted to HES equations." *)
      | Forall (x, psi) ->
          (* TODO: ∀は出力したほうがいい？ => 付けるべき。付けないとなぜか\がつくことがある *)
          if show_forall then (
            show_paren (prec > Prec.abs) ppf "@[<1>∀%a.@,%a@]"
              id' x
              (* (argty (Prec.(succ arrow))) x.ty *)
              (go_ Prec.abs) psi
          ) else (
            go_ Prec.abs ppf psi
          )
      | Exists (x, psi) -> 
        show_paren (prec > Prec.abs) ppf "@[<1>∃%a.@,%a@]"
            id' x
            (* (argty (Prec.(succ arrow))) x.ty *)
            (go_ Prec.abs) psi
      | App (psi1, psi2) ->
          show_paren (prec > Prec.app) ppf "@[<1>%a@ %a@]"
            (go_ Prec.app) psi1
            (go_ Prec.(succ app)) psi2
      | Arith a ->
          arith_ prec ppf a
      | Pred (pred, as') ->
          show_paren (prec > Prec.eq) ppf "%a"
            formula (Formula.Pred(pred, as'))
    in go_

  let hflz' : (Prec.t -> 'ty Fmt.t) -> bool -> 'ty Hflz.t Fmt.t =
    fun format_ty_ show_forall -> hflz_' format_ty_ show_forall Prec.zero
  
  let hflz_hes_rule' : (Prec.t -> 'ty Fmt.t) -> bool -> 'ty Hflz.hes_rule Fmt.t =
    fun format_ty_ show_forall ppf rule ->
      let args, phi = Hflz.decompose_abs rule.body in
      (* 'ty Type.arg Id.t を表示したい *)
      Fmt.pf ppf "@[<2>%s %a =%a@ %a.@]"
        (replace_apos @@ Id.to_string rule.var)
        (pp_print_list ~pp_sep:fprint_space id') args
        (* (format_ty_ Prec.zero) rule.var.ty *)
        fixpoint rule.fix
        (hflz' format_ty_ show_forall) phi
  
  let hflz_hes' : (Prec.t -> 'ty Fmt.t) -> bool -> 'ty Hflz.hes Fmt.t =
    fun format_ty_ show_forall ppf hes ->
      Fmt.pf ppf "@[<v>%a@]"
        (Fmt.list (hflz_hes_rule' format_ty_ show_forall)) hes
    
  let save_hes_to_file show_forall hes =
    Random.self_init ();
    let r = Random.int 0x10000000 in
    let file = Printf.sprintf "/tmp/%s-%d.smt2" "nuonly" r in
    let oc = open_out file in
    let fmt = Format.formatter_of_out_channel oc in
    Format.pp_set_margin fmt 1000;
    Printf.fprintf oc "%%HES\n" ;
    hflz_hes' Hflmc2_syntax.Print.simple_ty_ show_forall fmt hes;
    Format.pp_print_flush fmt ();
    close_out oc;
    file
end

let show_hflz = Hflmc2_util.fmt_string (hflz Hflmc2_syntax.Print.simple_ty_)
let show_hflz_full v = Hflz.show (fun fmt ty_ -> Hflmc2_syntax.Type.pp_simple_ty fmt ty_) v
let show_hes hes : string =
  List.map
    (fun rule ->
      "{" ^
      "fix: " ^ (Hflmc2_syntax.Fixpoint.show rule.fix) ^ "\n" ^
      "var: " ^ (Id.show Hflmc2_syntax.Type.pp_simple_ty rule.var) ^ "\n" ^
      "body: " ^ (show_hflz rule.body) ^ 
      "}"
    ) hes
  |> String.concat "\n"