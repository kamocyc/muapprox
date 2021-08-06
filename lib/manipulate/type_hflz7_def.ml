open Hflmc2_syntax

let simplified_type = ref false
let output_debug_info = ref false

let save_to_file file text =
  let oc = open_out file in
  output_string oc text;
  close_out oc

type 'ty tarith = 'ty Id.t Arith.gen_t
[@@deriving eq,ord,show]

type 'ty thflz =
  | Bool   of bool
  | Var    of 'ty Id.t
  | Or     of 'ty thflz * 'ty thflz
  | And    of 'ty thflz * 'ty thflz
  | Abs    of 'ty Id.t * 'ty thflz * 'ty
  | Forall of 'ty Id.t * 'ty thflz
  | Exists of 'ty Id.t * 'ty thflz
  | App    of 'ty thflz * 'ty thflz
  | Arith  of 'ty tarith
  | Pred   of Formula.pred * 'ty tarith list
  [@@deriving eq,ord,show]

type use_flag = TUse | TNotUse | EFVar of unit Hflmc2_syntax.Id.t
[@@deriving eq,ord,show]

type fixpoint = Least | Greatest | NonRecursive
[@@deriving eq,ord,show]

type ptype = TInt | TBool | TFunc of ptype * ptype * use_flag | TVar of unit Hflmc2_syntax.Id.t
[@@deriving eq,ord,show]

type 'a in_out = {inner_ty: 'a; outer_ty: 'a}
[@@deriving eq,ord,show]

type 'a thes_rule = {var: 'a in_out Id.t; body: 'a thflz; fix: fixpoint}
[@@deriving eq,ord,show]

type s_thes_rules = ptype thes_rule list
[@@deriving eq,ord,show]

type use_flag_constraint = EF_Equal of use_flag * use_flag | EF_Le of use_flag * use_flag
[@@deriving eq,ord,show]

type recursive_flag = Recursive | NotRecursive
[@@deriving eq,ord,show]

let get_thflz_type_without_check phi =
  let rec go phi = match phi with
    | Bool _ -> TBool
    | Var v -> v.ty
    | Or _ -> TBool
    | And _ -> TBool
    | Abs (_, _, lty) -> lty
    | Forall (_, body) -> go body
    | Exists (_, body) -> go body
    | App (p1, _) -> begin
      let ty1 = go p1 in
      match ty1 with
      | TFunc (_, t2, _) -> t2
      | _ -> assert false
    end
    | Pred (_, _) -> TBool
    | Arith _ -> TInt
  in
  go phi

let show_fixpoint = function
  | Least -> "μ"
  | Greatest -> "ν"
  | NonRecursive -> ""

let show_use_flag = function
  | TUse -> "T"
  | TNotUse -> "_"
  | EFVar id -> Hflmc2_syntax.Id.to_string id

let rec pp_ptype prec ppf ty =
  if !simplified_type then begin
    match ty with
    | TBool ->
      Fmt.pf ppf "bool"
    | TInt ->
      Fmt.pf ppf "int"
    | TFunc (ty1, ty2, f) ->
      Print.show_paren (prec > Print.Prec.arrow) ppf "@[<1>[%a,%s] ->@ %a@]"
        (pp_ptype Print.Prec.(succ arrow)) ty1
        (show_use_flag f)
        (pp_ptype Print.Prec.arrow) ty2
    | TVar (id) ->
      Fmt.pf ppf "%s" (Id.to_string id)
  end else begin
    match ty with
    | TBool ->
      Fmt.pf ppf "bool"
    | TInt ->
      Fmt.pf ppf "int"
    | TFunc (ty1, ty2, f) ->
      Print.show_paren (prec > Print.Prec.arrow) ppf "@[<1>%a -%s->@ %a@]"
      (* Print.show_paren (prec > Print.Prec.arrow) ppf "@[<1>[%a,%s] ->@ %a@]" *)
        (pp_ptype Print.Prec.(succ arrow)) ty1
        (show_use_flag f)
        (pp_ptype Print.Prec.arrow) ty2
    | TVar (id) ->
      Fmt.pf ppf "%s" (Id.to_string id)
  end

let show_ptype = Hflmc2_util.fmt_string (pp_ptype Print.Prec.zero)

let show_use_flag_constraint = function
  | EF_Equal (f1, f2) -> show_use_flag f1 ^ "=" ^ show_use_flag f2
  | EF_Le (f1, f2) -> show_use_flag f1 ^ "<=" ^ show_use_flag f2

let get_args phi =
  let rec go phi = match phi with
    | Abs (x, p, _ty) ->
      let xs, r = go p in
      x :: xs, r
    | _ -> [], phi
  in
  go phi  
  
module Print_temp = struct
  open Hflmc2_syntax.Print

  let rec gen_arith_ : 'avar t_with_prec -> 'pty tarith t_with_prec =
    fun avar_ prec ppf a ->
      let show_op = function | (Arith.Op (op',[a1;a2])) -> begin
        let op_prec = Prec.of_op op' in
        let prec_l = Prec.(succ_if (not @@ op_is_leftassoc op') op_prec) in
        let prec_r = Prec.(succ_if (not @@ op_is_rightassoc op') op_prec) in
        show_paren (prec > op_prec) ppf "@[<1>%a@ %a@ %a@]"
          (gen_arith_ avar_ prec_l) a1
          op op'
          (gen_arith_ avar_ prec_r) a2
      end | _ -> assert false
      in
      match a with
      | Int (n) ->
        if n >= 0 then
          Fmt.int ppf n
        else
          (Fmt.string ppf "("; Fmt.int ppf n; Fmt.string ppf ")";)
      | Var (x) -> avar_ prec ppf x
      | Op (_, _) -> show_op a
      
  let id_ (_prec : prec) (ppf : formatter) (x : 'pty Id.t) = id ppf x
  let arith_ (prec : Prec.t) (ppf: formatter) (a : 'pty Id.t Arith.gen_t)
    = gen_arith_ id_ prec ppf a
  
  let ptype_to_flag_string ty =
    match ty with
    | TFunc (_, _, f) -> show_use_flag f
    | _ -> ""
  
  let thflz_to_ptype = get_thflz_type_without_check
  
  let rec hflz_ (get_type : 'pty thflz -> 'pty) (show_flag : 'pty -> string) (format_ty_ : Prec.t -> 'pty Fmt.t) (prec : Prec.t) (ppf : formatter) (phi : 'pty thflz) = match phi with
      | Bool true -> Fmt.string ppf "true"
      | Bool false -> Fmt.string ppf "false"
      | Var x ->
        if !output_debug_info then
          Fmt.pf ppf "(%a : %a)" id x (format_ty_ Prec.zero) x.ty
        else
          Fmt.pf ppf "%a" id x
      | Or (phi1,phi2)  ->
          (* p_id ppf sid;  *)
          show_paren (prec > Prec.or_) ppf "@[<hv 0>%a@ \\/ %a@]"
            (hflz_ get_type show_flag format_ty_ Prec.or_) phi1
            (hflz_ get_type show_flag format_ty_ Prec.or_) phi2
      | And (phi1,phi2)  ->
          (* p_id ppf sid;  *)
          show_paren (prec > Prec.and_) ppf "@[<hv 0>%a@ /\\ %a@]"
            (hflz_ get_type show_flag format_ty_ Prec.and_) phi1
            (hflz_ get_type show_flag format_ty_ Prec.and_) phi2
      | Abs (x, psi, ty) -> begin
          let f_str = show_flag ty in
          if !output_debug_info then
            show_paren (prec > Prec.abs) ppf "@[<1>(λ%a:{%s}%a.@,%a){%a}@]"
              id x
              f_str
              (format_ty_ Prec.(succ arrow)) x.ty
              (hflz_ get_type show_flag format_ty_ Prec.abs) psi
              (format_ty_ Prec.(succ arrow)) ty
          else
            show_paren (prec > Prec.abs) ppf "@[<1>λ%a:{%s}%a.@,%a@]"
              id x
              f_str
              (format_ty_ Prec.(succ arrow)) x.ty
              (hflz_ get_type show_flag format_ty_ Prec.abs) psi
      end
      | Forall (x, psi) ->
          show_paren (prec > Prec.abs) ppf "@[<1>∀%a.@,%a@]"
            id x
            (hflz_ get_type show_flag format_ty_ Prec.abs) psi
      | Exists (x, psi) ->
          show_paren (prec > Prec.abs) ppf "@[<1>∃%a.@,%a@]"
            id x
            (hflz_ get_type show_flag format_ty_ Prec.abs) psi
      | App (psi1, psi2) -> begin
          let ty = get_type psi1 in
          let f_str = show_flag ty in
          show_paren (prec > Prec.app) ppf "@[<1>%a@ %s%a@]"
            (hflz_ get_type show_flag format_ty_ Prec.app) psi1
            f_str
            (hflz_ get_type show_flag format_ty_ Prec.(succ app)) psi2
      end
      | Arith a ->
        arith_ prec ppf a
      | Pred (pred', [f1; f2]) ->
          (* p_id ppf sid;  *)
          Fmt.pf ppf "@[<1>%a@ %a@ %a@]"
            (arith_ prec) f1
            pred pred'
            (arith_ prec) f2
      | Pred _ -> assert false

  let hflz_ : ('pty thflz -> 'pty) -> ('pty -> string) -> (Prec.t -> 'ty Fmt.t) -> 'ty thflz Fmt.t =
    fun get_type show_flag format_ty_ -> hflz_ get_type show_flag format_ty_ Prec.zero

  let hflz : (Prec.t -> 'ty Fmt.t) -> 'ty thflz Fmt.t =
    hflz_ thflz_to_ptype ptype_to_flag_string
  
  let hflz_hes_rule : (Prec.t -> 'ty Fmt.t) -> 'ty thes_rule Fmt.t =
    fun format_ty_ ppf {var; body; fix} ->
      let rec to_flags ty =
        match ty with
        | TFunc (_, ty, f) -> f :: to_flags ty
        | _ -> []
      in
      let {outer_ty; inner_ty} = var.ty in
      let args, body = get_args body in
      Fmt.pf ppf "@[<2>%s %a =%s@ %a@]"
        (Id.to_string var)
        (pp_print_list ~pp_sep:Print_syntax.PrintUtil.fprint_space (fun ppf ((arg, _f1), f2) -> fprintf ppf "(%s : {%s}(%a))" (Id.to_string arg) (show_use_flag f2) (format_ty_ Prec.zero) arg.Id.ty))
        (List.combine (List.combine args (to_flags outer_ty)) (to_flags inner_ty))
        (show_fixpoint fix)
        (hflz_ thflz_to_ptype ptype_to_flag_string format_ty_) body

  let hflz_hes :  (Prec.t -> 'ty Fmt.t) -> 'ty thes_rule list Fmt.t =
    fun format_ty_ ppf rules ->
      Fmt.pf ppf "@[<v>%a@]"
        (Fmt.list (hflz_hes_rule format_ty_)) rules
end

let dummy_use_flag = EFVar (Id.gen ())

let get_free_variables phi =
  let rec go phi = match phi with
    | Bool _ -> []
    | Var v -> [v]
    | Or (p1, p2) -> go p1 @ go p2
    | And (p1, p2) -> go p1 @ go p2
    | Abs (x, p, _) -> List.filter (fun v -> not @@ Id.eq x v) (go p)
    | Forall (x, p) -> List.filter (fun v -> not @@ Id.eq x v) (go p)
    | Exists (x, p) -> List.filter (fun v -> not @@ Id.eq x v) (go p)
    | App (p1, p2) -> go p1 @ go p2
    | Arith a -> go_arith a
    | Pred (_, ps) -> List.map go_arith ps |> List.concat
  and go_arith a = match a with
    | Int _ -> []
    | Var v -> [v]
    | Op (_, ps) -> List.map go_arith ps |> List.concat
  in
  go phi

let id_gen ?name ty = 
  let id = Id.gen ?name ty in
  { id with name = id.name ^ string_of_int id.id }
