let partition = List.partition

open Core open Core.Poly

(** First-Order Fixpoint Logic with Theories *)
type fun_sym = ..
type fun_sym += FunCall of string
type pred_sym = ..

module Sort = struct
  type t = ..
  type t += SDummy
end

type info = ..
type info += Dummy
type info += ApproxConstraint of bool (* is parameter? *)

type parsed
type fixpoint_free

module rec Term : sig
  type t =
    | Var of Ident.tvar * Sort.t * info
    | FunApp of fun_sym * t list * info

  (** constructor *)
  val mk_var: Ident.tvar -> Sort.t -> info -> t
  val mk_funapp: fun_sym -> t list -> info -> t

  (** test *)
  val is_var: t -> bool
  val is_funapp: t -> bool
  val is_funcall: t -> bool

  (** destructor *)
  val let_var: t -> Ident.tvar * Sort.t * info
  val let_funapp: t -> fun_sym * t list * info
  val let_funcall: t -> string * t list * info

  (** substitution *)
  val rename: (Ident.tvar, Ident.tvar) Map.Poly.t -> t -> t
  val rename_fun_sym: (Ident.tvar, Ident.tvar) Map.Poly.t -> fun_sym -> fun_sym
  val subst: (Ident.tvar, t) Map.Poly.t -> t -> t
  val subst_fun_sym: (Ident.tvar, t) Map.Poly.t -> fun_sym -> fun_sym
  val replace_pred_ident : Ident.pvar -> Ident.pvar -> t -> t

  val get_ftv: t -> Ident.tvar Set.Poly.t
  val get_ftv_sort: t -> (Ident.tvar * Sort.t) Set.Poly.t

  val ast_size: t -> int

  val refresh_pvar : t -> t
  val extend_pred_params : Ident.pvar -> (Ident.tvar * Sort.t) list -> t -> t

  val str_of: t -> string

  val simplify: t -> t
end = struct
  type t =
    | Var of Ident.tvar * Sort.t * info
    | FunApp of fun_sym * t list * info

  (** constructor *)
  let mk_var var sort info = Var(var, sort, info)
  let mk_funapp sym ts info = FunApp(sym, ts, info)

  (** test *)
  let is_var = function Var(_, _, _) -> true | _ -> false
  let is_funapp = function FunApp(_, _, _) -> true | _ -> false
  let is_funcall = function FunApp(FunCall _, _, _) -> true | _ -> false

  (** destructor *)
  let let_var = function
    | Var(var, sort, info) -> (var, sort, info)
    | _ -> assert false
  let let_funapp = function
    | FunApp(sym, ts, info) -> (sym, ts, info)
    | _ -> assert false
  let let_funcall = function
    | FunApp(FunCall funname, ts, info) -> (funname, ts, info)
    | _ -> assert false

  (** substitution *)
  let rec rename maps = function
    | Var(var', sort, info) -> begin
        match Map.Poly.find maps var' with
        | None -> Var(var', sort, info)
        | Some var -> Var(var, sort, info)
      end
    | FunApp (sym, ts, info) ->
      FunApp (rename_fun_sym maps sym, List.map ~f:(rename maps) ts, info)

  and rename_fun_sym maps = function
    | T_bool.Bool atom -> T_bool.Bool(Atom.rename maps atom)
    | T_bool.Formula phi -> T_bool.Formula(Formula.rename maps phi)
    | sym -> sym

  let rec subst maps = function
    | Var(var', sort, info) -> begin
        match Map.Poly.find maps var' with
        | None -> Var(var', sort, info)
        | Some t -> t
      end
    | FunApp (sym, ts, info) ->
      FunApp (subst_fun_sym maps sym, List.map ~f:(subst maps) ts, info)

  and subst_fun_sym maps = function
    | T_bool.Bool atom -> T_bool.Bool(Atom.subst maps atom)
    | T_bool.Formula phi -> T_bool.Formula(Formula.subst maps phi)
    | sym -> sym

  let rec replace_pred_ident from to_ = function
    | FunApp (sym, args, info) ->
      let args = List.map ~f:(fun arg -> replace_pred_ident from to_ arg) args in
      FunApp (sym, args, info)
    | x -> x

  let rec get_ftv = function
    (* | Var(tvar, T_int.SUnrefInt, _) -> failwith @@ Printf.sprintf "type of %s is T_int.SUnrefInt" (Ident.name_of_tvar tvar)
       | Var(tvar, T_int.SRefInt, _) -> failwith @@ Printf.sprintf "type of %s is T_int.SRefInt" (Ident.name_of_tvar tvar) *)
    | Var(tvar, _, _) -> Set.Poly.singleton tvar
    | FunApp(sym, args, _) ->
      let sym_fv =
        match sym with
        | T_bool.Bool atom -> Atom.get_ftv atom
        | T_bool.Formula phi -> Formula.get_ftv phi
        | _ -> Set.Poly.empty
      in
      (sym_fv :: List.map args ~f:get_ftv)
      |> Set.Poly.union_list

  let rec get_ftv_sort = function
    | Var(var, sort, _) -> Set.Poly.singleton (var, sort)
    | FunApp(sym, args, _) ->
      let sym_fv =
        match sym with
        | T_bool.Bool atom -> Atom.get_ftv_sort atom
        | T_bool.Formula phi -> Formula.get_ftv_sort phi
        | _ -> Set.Poly.empty
      in
      (sym_fv :: List.map args ~f:get_ftv_sort)
      |> Set.Poly.union_list

  let ast_size = function
    | Var(_, _, _) -> 1
    | FunApp(sym, args, _) ->
      let size_of_args = List.fold_left ~f:(fun acc term -> acc + Term.ast_size term) ~init:1 args in
      match sym with
      | T_bool.Formula phi -> size_of_args + (Formula.ast_size phi)
      | _ -> size_of_args

  let refresh_pvar = function
    | Var (var, sort, info) -> Var (var, sort, info)
    | FunApp (sym, args, info) -> begin
        let sym = match sym with
          | T_bool.Bool atom -> T_bool.Bool (Atom.refresh_pvar atom)
          | T_bool.Formula phi -> T_bool.Formula (Formula.refresh_pvar phi)
          | x -> x
        in
        let args = List.map ~f:(fun arg -> Term.refresh_pvar arg) args in
        FunApp (sym, args, info)
      end

  let rec extend_pred_params ident extended_params = function
    | FunApp (sym, args, info) -> begin
        let args = List.map ~f:(extend_pred_params ident extended_params) args in
        let sym = match sym with
          | T_bool.Bool atom -> T_bool.Bool (Atom.extend_pred_params ident extended_params atom)
          | T_bool.Formula phi -> T_bool.Formula (Formula.extend_pred_params ident extended_params phi)
          | x -> x
        in
        FunApp (sym, args, info)
      end
    | x -> x

  let str_of_fun_sym = function
    | T_int.Add -> "T_int.Add" | T_int.Div -> "T_int.Div" | T_int.Mod -> "T_int.Mod" | T_int.Mult -> "T_int.Mult"
    | T_int.Real s -> Printf.sprintf "T_int.Real %s" s
    | T_int.Int i -> Printf.sprintf "T_int.Int %s" (Bigint.to_string_hum i)
    | T_int.Sub -> "T_int.Sub" | T_int.UnaryNeg -> "T_int.UnaryNeg"
    | T_bool.Bool atom -> Printf.sprintf "T_bool.Bool %s" (Atom.str_of atom)
    | T_bool.Formula phi -> Printf.sprintf "T_bool.Formula (%s)" (Formula.str_of phi)
    | T_bool.IfThenElse -> "IfThenElse"
    | _ -> failwith "unimplemented function symbols"

  let rec str_of = function
    | Var (Ident.Tvar id, _, _) -> Printf.sprintf "Var (%s)" id
    | FunApp (fun_sym, terms, _) -> Printf.sprintf "FunApp (%s, %s)" (str_of_fun_sym fun_sym)
                                      (List.fold_left ~f:(fun acc term -> acc ^ ", " ^ (str_of term)) ~init:"" terms)

  let rec simplify term =
    match term with
    | Var _ -> term
    | FunApp (fun_sym, terms, info) ->
      let terms = List.map ~f:simplify terms in
      match terms with
      | [FunApp (T_int.Int a, [], _)] ->
        if fun_sym = T_int.UnaryNeg then
          FunApp (T_int.Int (Bigint.neg a), [], info)
        else
          FunApp(fun_sym, terms, info)
      | [FunApp (T_int.Int a, [], _); FunApp (T_int.Int b, [], _)] ->
        (match fun_sym with
         | T_int.Add | T_int.Sub | T_int.Mult | T_int.Mod ->
           FunApp (T_int.Int ((T_int.binfun_of_fsym fun_sym) a b), [], info)
         | _ ->
           FunApp(fun_sym, terms, info)
        )
      | _ ->
        FunApp(fun_sym, terms, info)

end

and Predicate : sig
  type fixpoint = Mu | Nu

  type t =
    | Var of Ident.pvar * Sort.t list
    | Psym of pred_sym
    | Fixpoint of fixpoint * Ident.pvar * (Ident.tvar * Sort.t) list * Formula.t

  val is_var: t -> bool
  val is_psym: t -> bool
  val is_fix: t -> bool
  val let_var: t -> Ident.pvar * Sort.t list
  val let_psym: t -> pred_sym
  val let_fix: t -> fixpoint * Ident.pvar * (Ident.tvar * Sort.t) list * Formula.t
  val mk_var: Ident.pvar -> Sort.t list -> t
  val mk_psym: pred_sym -> t
  val mk_fix: fixpoint -> Ident.pvar -> (Ident.tvar * Sort.t) list -> Formula.t -> t

  val rename: (Ident.tvar, Ident.tvar) Map.Poly.t -> Predicate.t -> Predicate.t
  val rename_preds: (Ident.pvar, Ident.pvar) Map.Poly.t -> t -> t
  val subst: (Ident.tvar, Term.t) Map.Poly.t -> Predicate.t -> Predicate.t
  val replace_pred_ident : Ident.pvar -> Ident.pvar -> t -> t
  val subst_neg: Ident.pvar -> t -> t
  val simplify: t -> t
  val simplify_neg: t -> t
  val get_ftv: t -> Ident.tvar Set.Poly.t
  val get_ftv_sort: t -> (Ident.tvar * Sort.t) Set.Poly.t
  val get_fpv: t -> Ident.pvar Set.Poly.t
  val flip_fixpoint: fixpoint -> fixpoint

  val refresh_pvar : t -> t
  val extend_pred_params: Ident.pvar -> (Ident.tvar * Sort.t) list -> t -> t
  val refresh_tvar : t -> t

  (* attributes *)
  val nesting_level: t -> int
  val number_of_quantifiers: t -> int

  val str_of: t -> string
end = struct
  type fixpoint = Mu | Nu

  type t =
    | Var of Ident.pvar * Sort.t list
    | Psym of pred_sym
    | Fixpoint of fixpoint * Ident.pvar * (Ident.tvar * Sort.t) list * Formula.t

  let is_var = function Var _ -> true | _ -> false
  let is_psym = function Psym _ -> true | _ -> false
  let is_fix = function Fixpoint _ -> true | _ -> false
  let let_var = function Var (pvar, sort) -> (pvar, sort) | _ -> assert false
  let let_psym = function Psym psym -> psym | _ -> assert false
  let let_fix = function Fixpoint (fix, pvar, args, body) -> (fix, pvar, args, body) | _ -> assert false
  let mk_var pvar sort = Var (pvar, sort)
  let mk_psym psym = Psym psym
  let mk_fix fix pvar args body = Fixpoint (fix, pvar, args, body)

  let flip_fixpoint = function Mu -> Nu | Nu -> Mu

  let refresh_pvar = function
    | Var (pvar, sorts) -> Var (pvar, sorts)
    | Psym sym -> Psym sym
    | Fixpoint (fp, pvar, params, body) ->
      let fresh = Ident.mk_fresh_pvar () in
      let body = Formula.replace_pred_ident pvar fresh body in
      let body = Formula.refresh_pvar body in
      Fixpoint (fp, fresh, params, body)

  let extend_pred_params ident extended_params = function
    | Fixpoint (fp, pvar, params, body) ->
      let body = Formula.extend_pred_params ident extended_params body in
      Fixpoint (fp, pvar, params, body)
    | x -> x

  let refresh_tvar = function
    | Var (pvar, sorts) -> Var (pvar, sorts)
    | Psym sym -> Psym sym
    | Fixpoint (fp, pvar, params, body) ->
      let params' = List.map
          ~f:(fun (_, s) -> (Ident.mk_fresh_tvar(), s)) params in
      let map = List.zip_exn params params'
                |> List.map
                  ~f:(fun ((t, _),(t', s)) ->
                      (t, Term.mk_var t' s Dummy))
                |> Map.Poly.of_alist_exn in
      Fixpoint (fp, pvar, params',
                Formula.refresh_tvar @@ Formula.subst map body)

  let rename maps = function
    | Var (var, sort) -> Var (var, sort)
    | Psym sym -> Psym sym
    | Fixpoint (fixpoint, pvar, bounds, body) ->
      let maps =
        List.fold ~init:maps ~f:(fun maps (var, _) -> Map.Poly.remove maps var) bounds
      in
      Fixpoint(fixpoint, pvar, bounds, Formula.rename maps body)

  let rename_preds maps = function
    | Var (pvar, sort) ->
      begin
        match Map.Poly.find maps pvar with
        | None -> Var (pvar, sort)
        | Some pvar' -> Var (pvar', sort)
      end
    | Psym sym -> Psym sym
    | Fixpoint (fixpoint, pvar, bounds, body) ->
      let pvar' = match Map.Poly.find maps pvar with None -> pvar | Some pvar' -> pvar' in
      Fixpoint(fixpoint, pvar', bounds, Formula.rename_preds maps body)

  let subst maps = function
    | Var (var, sort) -> Var (var, sort)
    | Psym sym -> Psym sym
    | Fixpoint (fixpoint, pvar, bounds, body) ->
      let maps =
        List.fold ~init:maps ~f:(fun maps (var, _) -> Map.Poly.remove maps var) bounds
      in
      Fixpoint(fixpoint, pvar, bounds, Formula.subst maps body)

  let replace_pred_ident from to_ = function
    | Psym x -> Psym x
    | Var (var, sort) when var = from -> Var (to_, sort)
    | Var (var, sort) -> Var (var, sort)
    | Fixpoint (fp, pvar, bounds, body) ->
      if pvar = from then
        Fixpoint (fp, pvar, bounds, body)
      else
        Fixpoint (fp, pvar, bounds, Formula.replace_pred_ident from to_ body)


  let subst_neg pvar = function
    | Var (pvar', sort) ->
      if pvar' = pvar then assert false (* it must be handled with Formula.subst_neg *)
      else Var (pvar', sort)
    | Psym psym -> Psym psym
    | Fixpoint (fixpoint, pvar', bounds, body) ->
      if pvar' = pvar then assert false
      else Fixpoint (fixpoint, pvar', bounds, Formula.subst_neg pvar body)

  let simplify = function
    | Var (var, sort) -> Var (var, sort)
    | Psym psym -> Psym psym
    | Fixpoint (fixpoint, pvar, bounds, body) ->
      Fixpoint(fixpoint, pvar, bounds, Formula.simplify body)

  let simplify_neg = function
    | Var _ -> assert false (* handled with Formula.simplify_neg *)
    | Psym T_int.Leq -> Psym T_int.Gt
    | Psym T_int.Geq -> Psym T_int.Lt
    | Psym T_int.Lt -> Psym T_int.Geq
    | Psym T_int.Gt -> Psym T_int.Leq
    | Psym T_bool.Eq -> Psym T_bool.Neq
    | Psym T_bool.Neq -> Psym T_bool.Eq
    | Psym _ -> assert false
    | Fixpoint (fixpoint, pvar, bounds, body) ->
      let body = Formula.subst_neg pvar body in
      Fixpoint(flip_fixpoint fixpoint, pvar, bounds, Formula.simplify_neg body)

  let get_ftv = function
    | Var _ -> Set.Poly.empty
    | Psym _ -> Set.Poly.empty
    | Fixpoint (_, _, bounds, body) ->
      Set.Poly.diff (Formula.get_ftv body) (bounds |> List.map ~f:fst |> Set.Poly.of_list)

  let get_ftv_sort = function
    | Var _ -> Set.Poly.empty
    | Psym _ -> Set.Poly.empty
    | Fixpoint (_, _, bounds, body) ->
      Set.Poly.diff (Formula.get_ftv_sort body) (bounds |> Set.Poly.of_list)

  let get_fpv = function
    | Var (pvar, _) -> Set.Poly.singleton pvar
    | Psym _ -> Set.Poly.empty
    | Fixpoint (_, pvar, _, body) ->
      Set.Poly.remove (Formula.get_fpv body) pvar

  let nesting_level =function
    | Fixpoint (_, _, _, phi) ->
      1 + (Formula.nesting_level phi)
    | _ -> 0

  let number_of_quantifiers = function
    | Fixpoint (_, _, _, phi) -> Formula.number_of_quantifiers phi
    | _ -> 0

  let str_of_predsym = function
    | T_bool.Eq -> "T_bool.Eq" | T_bool.Neq -> "T_bool.Neq"
    | T_int.Leq -> "T_int.Leq" | T_int.Lt -> "T_int.Lt" | T_int.Geq -> "T_int.Geq" | T_int.Gt -> "T_int.Gt"
    | _ -> failwith "undefineded predsymbol"

  let str_of = function
    | Var (Ident.Pvar id, _) -> Printf.sprintf "Var (%s)" id
    | Psym symbol -> Printf.sprintf "Psym %s" @@ str_of_predsym symbol
    | Fixpoint (_, _, _, _) -> "Fixpoint" (* TODO: implement *)
end

and Atom : sig
  type t =
    | True of info
    | False of info
    | App of Predicate.t * Term.t list * info

  (** constructor *)
  val mk_true: info -> t
  val mk_false: info -> t
  val mk_app: Predicate.t -> Term.t list -> info -> t
  val mk_varapp: Ident.pvar -> Term.t list -> info -> t

  (** test *)
  val is_true: t -> bool
  val is_false: t -> bool
  val is_app: t -> bool
  val is_varapp: t -> bool
  val is_symapp: t -> bool
  val occur: Ident.pvar -> t -> bool

  (** destructor *)
  val info_of_true: t -> info
  val info_of_false: t -> info
  val let_app: t -> Predicate.t * Term.t list * info
  val let_varapp: t -> Ident.pvar * Term.t list * info
  val let_symapp: t -> pred_sym * Term.t list * info

  (** aux *)
  val info_of: t -> info
  val simplify: t -> t
  val simplify_neg: t -> t

  (** substitution *)
  val rename: (Ident.tvar, Ident.tvar) Map.Poly.t -> t -> t
  val rename_preds: (Ident.pvar, Ident.pvar) Map.Poly.t -> t -> t
  val subst: (Ident.tvar, Term.t) Map.Poly.t -> t -> t
  val subst_pred: Ident.pvar -> (Ident.tvar * Sort.t) list -> Formula.t -> t -> Formula.t
  val subst_preds: (Ident.pvar, ((Ident.tvar * Sort.t) list * Formula.t)) Map.Poly.t -> t -> Formula.t
  val replace_pred_ident : Ident.pvar -> Ident.pvar -> t -> t
  val subst_neg: Ident.pvar -> t -> t
  val get_ftv: t -> Ident.tvar Set.Poly.t
  val get_ftv_sort: t -> (Ident.tvar * Sort.t) Set.Poly.t
  val get_fpv: t -> Ident.pvar Set.Poly.t

  val refresh_pvar : t -> t
  val extend_pred_params : Ident.pvar -> (Ident.tvar * Sort.t) list -> t -> t

  val refresh_tvar : t -> t

  (* attributes *)
  val nesting_level: t -> int
  val number_of_quantifiers: t -> int
  val number_of_pvar_apps: bool -> t -> int
  val count_pvar_apps: t -> (Ident.pvar * (int * int)) list
  val ast_size: t -> int

  val str_of: t -> string
end = struct
  type t =
    | True of info
    | False of info
    | App of Predicate.t * Term.t list * info

  (** constructor *)
  let mk_true info = True info
  let mk_false info = False info
  let mk_app pred args info = App(pred, args, info)
  let mk_varapp pvar args info =
    let sorts = List.map ~f:(fun _ -> T_int.SInt) args in (* TODO *)
    App(Predicate.mk_var pvar sorts, args, info)

  (** test *)
  let is_true = function True _ -> true | _ -> false
  let is_false = function False _ -> true | _ -> false
  let is_app = function App (_, _, _) -> true | _ -> false
  let is_varapp = function App(Predicate.Var _, _, _) -> true | _ -> false
  let is_symapp = function App(Predicate.Psym _, _, _) -> true | _ -> false


  (** destructor *)
  let info_of_true = function
    | True info -> info
    | _ -> assert false
  let info_of_false = function
    | False info -> info
    | _ -> assert false
  let let_app = function
    | App(pred, args, info) -> pred, args, info
    | _ -> assert false
  let let_varapp = function
    | App(Predicate.Var (pvar, _), args, info) -> pvar, args, info
    | _ -> assert false
  let let_symapp = function
    | App(Predicate.Psym sym, args, info) -> sym, args, info
    | _ -> assert false


  (** aux *)
  let info_of = function
    | True info -> info
    | False info -> info
    | App(_, _, info) -> info

  let simplify = function
    | True info -> True info
    | False info -> False info
    | App(pred, terms, info) ->
      let pred = Predicate.simplify pred in
      let terms = List.map ~f:Term.simplify terms in
      match pred, terms with
      | (Predicate.Psym psym, [Term.FunApp (T_int.Int a, [], _); Term.FunApp (T_int.Int b, [], _)]) ->
        if (T_int.binfun_of_psym psym) a b then
          True info
        else
          False info
      | _ -> App(pred, terms, info)

  let simplify_neg = function
    | True info -> False info
    | False info -> True info
    | App(pred, terms, info) -> App(Predicate.simplify_neg pred, terms, info)

  (** substitution *)
  let rename maps = function
    | True info -> True info
    | False info -> False info
    | App(pred, args, info) ->
      App(Predicate.rename maps pred, List.map ~f:(Term.rename maps) args, info)

  let rename_preds maps = function
    | True info -> True info | False info -> False info
    | App(pred, args, info) -> App(Predicate.rename_preds maps pred, args, info)

  let subst maps = function
    | True info -> True info
    | False info -> False info
    | App(pred, args, info) ->
      App(Predicate.subst maps pred, List.map ~f:(Term.subst maps) args, info)

  let make_map params args =
    let rec aux acc = function
      | [], [] -> acc
      | ((ident, _)::xs, y::ys) -> aux ((ident, y) :: acc) (xs, ys)
      | _ -> failwith "length of params and args must be same. @make_map params args"
    in
    aux [] (params, args)

  let subst_pred ident params phi =function
    | App(Predicate.Var (ident', _), args, _) when ident = ident' ->
      (* TODO : check whether args match sorts *)
      let map = make_map params args |> Map.Poly.of_alist_exn in
      Formula.subst map phi
    | App(Predicate.Fixpoint (_, ident', _, _), _, _) as x
      when ident = ident' -> Formula.mk_atom x Dummy
    | App(Predicate.Fixpoint (fp, id, params', phi'), terms, info) ->
      Formula.mk_atom (App(Predicate.Fixpoint
                             (fp, id, params',
                              Formula.subst_pred ident params phi phi'),
                           terms, info)) Dummy
    | x -> Formula.mk_atom x Dummy

  let subst_preds maps = function
    | App(Predicate.Var (ident, _), args, _) when Map.Poly.mem maps ident ->
      let (params, phi) = Map.Poly.find_exn maps ident in
      let map = make_map params args |> Map.Poly.of_alist_exn in
      Formula.subst map phi
    | App(Predicate.Fixpoint (_, ident, _, _), _, _) as x
      when Map.Poly.mem maps ident -> Formula.mk_atom x Dummy
    | App(Predicate.Fixpoint (fp, id, params, phi), terms, info) ->
      Formula.mk_atom (App(Predicate.Fixpoint
                             (fp, id, params,
                              Formula.subst_preds maps phi),
                           terms, info)) Dummy
    | x -> Formula.mk_atom x Dummy

  let replace_pred_ident from to_ = function
    | App (pred, args, info) ->
      let pred = Predicate.replace_pred_ident from to_ pred in
      let args = List.map ~f:(fun arg -> Term.replace_pred_ident from to_ arg) args in
      App (pred, args, info)
    | x -> x

  let subst_neg pvar = function
    | True info -> True info
    | False info -> False info
    | App(pred, args, info) ->
      App(Predicate.subst_neg pvar pred, args, info)

  let get_ftv = function
    | True _ | False _ -> Set.Poly.empty
    | App(pred, args, _) ->
      (Predicate.get_ftv pred :: List.map args ~f:Term.get_ftv)
      |> Set.Poly.union_list

  let get_ftv_sort = function
    | True _ | False _ -> Set.Poly.empty
    | App(pred, args, _) ->
      (Predicate.get_ftv_sort pred :: List.map args ~f:Term.get_ftv_sort)
      |> Set.Poly.union_list

  let get_fpv = function
    | True _ | False _ -> Set.Poly.empty
    | App(pred, _, _) -> Predicate.get_fpv pred

  let refresh_pvar = function
    | True info -> True info
    | False info -> False info
    | App (pred, args, info) ->
      let pred = Predicate.refresh_pvar pred in
      let args = List.map ~f:(fun arg -> Term.refresh_pvar arg) args in
      App (pred, args, info)

  let extend_pred_params ident (extended_params: (Ident.tvar * Sort.t) list) = function
    | App (Predicate.Var (ident', params), args, info) when ident = ident' ->
      let extended_sorts: Sort.t list = AstUtil.sorts_of_params extended_params in
      let params = params @ extended_sorts in
      let extended_args = AstUtil.args_of_params extended_params in
      let args = args @ extended_args in
      App (Predicate.Var (ident, params), args, info)
    | App (pred, args, info) ->
      let pred = Predicate.extend_pred_params ident extended_params pred in
      let args = List.map ~f:(fun arg -> Term.extend_pred_params ident extended_params arg) args in
      App (pred, args, info)
    | x -> x

  let refresh_tvar = function
    | True info -> True info | False info -> False info
    | App (pred, args, info) ->
      App (Predicate.refresh_tvar pred, args, info)

  let nesting_level = function
    | True _ | False _ -> 0
    | App(pred, _, _) -> Predicate.nesting_level pred
  let number_of_quantifiers = function
    | True _ | False _ -> 0
    | App(pred, _, _) -> Predicate.number_of_quantifiers pred
  let number_of_pvar_apps is_pos = function
    | True _ | False _ -> 0
    | App(Predicate.Var _, _, _) -> if is_pos then 1 else 0
    | App(Predicate.Psym _, _, _) -> 0
    | App(Predicate.Fixpoint _, _, _) -> assert false (* This function does not support fixpoint fomulas appropriately *)
  let count_pvar_apps = function
    | True _ | False _ -> []
    | App(Predicate.Var (pvar, _), _, _) -> [pvar, (1, 0)]
    | App(Predicate.Psym _, _, _) -> []
    | App(Predicate.Fixpoint _, _, _) -> assert false

  let ast_size = function
    | True _ | False _ -> 1
    | App(Predicate.Var _, terms, _) | App(Predicate.Psym _, terms, _) ->
      (List.fold_left ~f:(fun acc term -> acc + Term.ast_size term) ~init:1 terms)
    | App(Predicate.Fixpoint (_, _, _, phi), terms, _) ->
      (List.fold_left ~f:(fun acc term -> acc + Term.ast_size term) ~init:(Formula.ast_size phi) terms)
  (** test *)
  let occur pv atom = Set.Poly.mem (get_fpv atom) pv

  let str_of = function
    | True _ -> "True" | False _ -> "False"
    | App(pred, terms, _) ->
      Printf.sprintf "App(%s, %s)"
        (Predicate.str_of pred)
        (List.fold_left ~f:(fun acc term -> acc ^ ", " ^ (Term.str_of term)) ~init:"" terms)
end

and Formula : sig
  type unop = Neg
  type binop = And | Or | Imply | Iff
  type binder = Forall | Exists

  type t =
    | Atom of Atom.t * info
    | UnaryOp of unop * t * info
    | BinaryOp of binop * t * t * info
    | Bind of binder * (Ident.tvar * Sort.t) list * t * info
    | LetRec of (Predicate.fixpoint * Ident.pvar * (Ident.tvar * Sort.t) list * Formula.t) list * Formula.t * info

  (** constructor *)
  val mk_atom: Atom.t -> info -> t

  val mk_unop: unop -> t -> info -> t
  val mk_neg: t -> info -> t

  val mk_binop: binop -> t -> t -> info -> t
  val mk_and: t -> t -> info -> t
  val mk_or: t -> t -> info -> t
  val mk_imply: t -> t -> info -> t
  val mk_iff: t -> t -> info -> t

  val mk_bind: binder -> (Ident.tvar * Sort.t) list -> t -> info -> t
  val mk_forall : (Ident.tvar * Sort.t) list -> t -> info -> t
  val mk_exists : (Ident.tvar * Sort.t) list -> t -> info -> t
  val mk_bind_if_bounded : binder -> (Ident.tvar * Sort.t) list -> t -> info -> t
  val mk_forall_if_bounded : (Ident.tvar * Sort.t) list -> t -> info -> t
  val mk_exists_if_bounded : (Ident.tvar * Sort.t) list -> t -> info -> t

  val mk_letrec : (Predicate.fixpoint * Ident.pvar * (Ident.tvar * Sort.t) list * Formula.t) list -> Formula.t -> info -> t

  val and_of: t list -> info -> t
  val or_of: t list -> info -> t

  val var : Ident.tvar -> t

  (** test *)
  val is_atom: t -> bool

  val is_unop: t -> bool
  val is_neg: t -> bool

  val is_binop: t -> bool
  val is_and: t -> bool
  val is_or: t -> bool
  val is_imply: t -> bool
  val is_iff: t -> bool

  val is_bind: t -> bool
  val is_forall: t -> bool
  val is_exists: t -> bool

  val is_letrec: t -> bool

  (** destructor *)
  val let_atom: t -> Atom.t * info

  val let_unop: t -> unop * Formula.t * info
  val let_neg: t -> Formula.t * info

  val let_binop: t -> binop * Formula.t * Formula.t * info
  val let_and: t -> Formula.t * Formula.t * info
  val let_or: t -> Formula.t * Formula.t * info
  val let_imply: t -> Formula.t * Formula.t * info
  val let_iff: t -> Formula.t * Formula.t * info

  val let_bind: t -> binder * (Ident.tvar * Sort.t) list * Formula.t * info
  val let_forall: t -> (Ident.tvar * Sort.t) list * Formula.t * info
  val let_exists: t -> (Ident.tvar * Sort.t) list * Formula.t * info
  val let_forall_or_formula: t -> (Ident.tvar * Sort.t) list * Formula.t * info
  val let_exists_or_formula: t -> (Ident.tvar * Sort.t) list * Formula.t * info

  val let_letrec: t -> (Predicate.fixpoint * Ident.pvar * (Ident.tvar * Sort.t) list * Formula.t) list * Formula.t * info

  (** subst *)
  val rename: (Ident.tvar, Ident.tvar) Map.Poly.t -> t -> t
  val rename_preds: (Ident.pvar, Ident.pvar) Map.Poly.t -> t -> t
  val subst: (Ident.tvar, Term.t) Map.Poly.t -> t -> t
  val subst_pred: Ident.pvar -> (Ident.tvar * Sort.t) list -> t -> t -> t
  val subst_preds: (Ident.pvar, ((Ident.tvar * Sort.t) list * t)) Map.Poly.t -> t -> t
  val replace_pred_ident: Ident.pvar -> Ident.pvar -> t -> t
  val subst_neg: Ident.pvar -> t -> t
  val subst_pvar: (Ident.pvar, t) Map.Poly.t -> t -> t

  (** aux *)
  val simplify: t -> t
  val simplify_neg: t -> t
  val flip_quantifier: binder -> binder
  (* TODO: return ftv with sort *)
  val get_ftv: t -> Ident.tvar Set.Poly.t
  val get_ftv_sort: t -> (Ident.tvar * Sort.t) Set.Poly.t
  val get_fpv: t -> Ident.pvar Set.Poly.t

  val refresh_pvar : t -> t
  val extend_pred_params : Ident.pvar -> (Ident.tvar * Sort.t) list -> t -> t
  val refresh_tvar : t -> t

  (** attributes *)
  val nesting_level: t -> int
  val number_of_quantifiers: t -> int
  val number_of_pvar_apps: bool -> t -> int
  val count_pvar_apps: t -> (Ident.pvar * (int * int)) list
  val ast_size: t -> int

  val atoms: t -> Atom.t Set.Poly.t
  val cnf_of: t -> (Atom.t list * Atom.t list * t) list
  val of_clause: (Atom.t list * Atom.t list * t) -> t
  val of_cnf: (Atom.t list * Atom.t list * t) list -> t

  val alpha_conv_clause: (Atom.t list * Atom.t list * t) -> (Atom.t list * Atom.t list * t)

  val str_of_binder: binder -> string
  val str_of_binop: binop -> string
  val str_of_unop: unop -> string
  val str_of: t -> string

end = struct
  type unop = Neg
  type binop = And | Or | Imply | Iff
  type binder = Forall | Exists

  type t =
    | Atom of Atom.t * info
    | UnaryOp of unop * Formula.t * info
    | BinaryOp of binop * Formula.t * Formula.t * info
    | Bind of binder * (Ident.tvar * Sort.t) list * Formula.t * info
    | LetRec of (Predicate.fixpoint * Ident.pvar * (Ident.tvar * Sort.t) list * Formula.t) list * Formula.t * info

  (** constructor *)
  let mk_atom atom info = Atom(atom, info)

  let mk_unop op phi info = UnaryOp(op, phi, info)
  let mk_neg phi info = UnaryOp(Neg, phi, info)

  let mk_binop op phi1 phi2 info = BinaryOp(op, phi1, phi2, info)
  let mk_and phi1 phi2 info = BinaryOp(And, phi1, phi2, info)
  let mk_or phi1 phi2 info = BinaryOp(Or, phi1, phi2, info)
  let mk_imply phi1 phi2 info = BinaryOp(Imply, phi1, phi2, info)
  let mk_iff phi1 phi2 info = BinaryOp(Iff, phi1, phi2, info)

  let mk_bind binder bound body info = Bind(binder, bound, body, info)
  let mk_forall bound body info = Bind(Forall, bound, body, info)
  let mk_exists bound body info = Bind(Exists, bound, body, info)
  let mk_bind_if_bounded binder bound body info = if bound = [] then body else mk_bind binder bound body info
  let mk_forall_if_bounded = mk_bind_if_bounded Forall
  let mk_exists_if_bounded = mk_bind_if_bounded Exists

  let mk_letrec funcs body info = LetRec(funcs, body, info)

  let and_of phis info =
    let rec aux acc = function
      | [] -> acc
      | Atom(Atom.True _, _) :: phis -> aux acc phis
      | Atom(Atom.False info', info) :: _ -> Atom(Atom.False info', info)
      | phi :: phis -> aux (mk_and acc phi info) phis
    in
    match phis with
    | [] -> Atom (Atom.True info, info)
    | x :: xs -> aux x xs

  let or_of phis info =
    let rec aux acc = function
      | [] -> acc
      | Atom(Atom.True info', info) :: _ -> Atom(Atom.True info', info)
      | Atom(Atom.False _, _) :: phis -> aux acc phis
      | phi :: phis -> aux (mk_or acc phi info) phis
    in
    match phis with
    | [] -> Atom (Atom.False info, info)
    | x :: xs -> aux x xs

  let var ident =
    Formula.mk_atom
      (Atom.mk_app
         (Predicate.Psym T_bool.Eq)
         [
           Term.mk_var ident T_bool.SBool Dummy;
           T_bool.mk_bool (Atom.mk_true Dummy) Dummy;
         ]
         Dummy)
      Dummy

  (** test *)
  let is_atom = function Atom(_, _) -> true | _ -> false
  let is_unop = function UnaryOp(_, _, _) -> true | _ -> false
  let is_neg = function UnaryOp(Neg, _, _) -> true | _ -> false
  let is_binop = function BinaryOp(_, _, _, _) -> true | _ -> false
  let is_and = function BinaryOp(And, _, _, _) -> true | _ -> false
  let is_or = function BinaryOp(Or, _, _, _) -> true | _ -> false
  let is_imply = function BinaryOp(Imply, _, _, _) -> true | _ -> false
  let is_iff = function BinaryOp(Iff, _, _, _) -> true | _ -> false
  let is_bind = function Bind(_, _, _, _) -> true | _ -> false
  let is_forall = function Bind(Forall, _, _, _) -> true | _ -> false
  let is_exists = function Bind(Exists, _, _, _) -> true | _ -> false
  let is_letrec = function LetRec _ -> true | _ -> false

  (** destructor *)
  let let_atom = function
    | Atom(atom, info) -> atom, info
    | _ -> assert false
  let let_unop = function
    | UnaryOp(op, phi, info) -> op, phi, info
    | _ -> assert false
  let let_neg = function
    | UnaryOp(Neg, phi, info) -> phi, info
    | _ -> assert false
  let let_binop = function
    | BinaryOp(op, phi1, phi2, info) -> op, phi1, phi2, info
    | _ -> assert false
  let let_and = function
    | BinaryOp(And, phi1, phi2, info) -> phi1, phi2, info
    | _ -> assert false
  let let_or = function
    | BinaryOp(Or, phi1, phi2, info) -> phi1, phi2, info
    | _ -> assert false
  let let_imply = function
    | BinaryOp(Imply, phi1, phi2, info) -> phi1, phi2, info
    | _ -> assert false
  let let_iff = function
    | BinaryOp(Iff, phi1, phi2, info) -> phi1, phi2, info
    | _ -> assert false
  let let_bind = function
    | Bind(binder, params, body, info) -> binder, params, body, info
    | _ -> assert false
  let let_forall = function
    | Bind(Forall, params, body, info) -> params, body, info
    | _ -> assert false
  let let_exists = function
    | Bind(Exists, params, body, info) -> params, body, info
    | _ -> assert false
  let let_forall_or_formula = function
    | Bind(Forall, params, body, info) -> params, body, info
    | fml -> [], fml, Dummy
  let let_exists_or_formula = function
    | Bind(Exists, params, body, info) -> params, body, info
    | fml -> [], fml, Dummy
  let let_letrec = function
    | LetRec(funcs, body, info) -> funcs, body, info
    | _ -> assert false


  let rec rename maps = function
    | Atom (atom, info) -> Atom (Atom.rename maps atom, info)
    | UnaryOp(Neg, phi, info) -> UnaryOp(Neg, rename maps phi, info)
    | BinaryOp(op, phi1, phi2, info) -> BinaryOp(op, rename maps phi1, rename maps phi2, info)
    | Bind(binder, bounds, body, info) ->
      let maps =
        List.fold ~init:maps ~f:(fun maps (var, _) -> Map.Poly.remove maps var) bounds
      in
      Bind(binder, bounds, rename maps body, info)
    | LetRec(funcs, body, info) ->
      let funcs =
        List.map ~f:(fun (fix, pvar, arg_sorts, func_body) ->
            let maps =
              List.fold ~init:maps ~f:(fun maps (var, _) -> Map.Poly.remove maps var) arg_sorts
            in
            (fix, pvar, arg_sorts, rename maps func_body)) funcs in
      LetRec(funcs, rename maps body, info)

  let rec rename_preds maps = function
    | Atom (atom, info) -> Atom (Atom.rename_preds maps atom, info)
    | UnaryOp(Neg, phi, info) -> UnaryOp(Neg, rename_preds maps phi, info)
    | BinaryOp(op, phi1, phi2, info) -> BinaryOp(op, rename_preds maps phi1, rename_preds maps phi2, info)
    | Bind(binder, bounds, body, info) ->
      Bind(binder, bounds, rename_preds maps body, info)
    | LetRec(funcs, body, info) ->
      let funcs =
        List.map funcs ~f:(fun (fix, pvar, arg_sorts, func_body) ->
            (fix, pvar, arg_sorts, rename_preds maps func_body))
      in LetRec(funcs, rename_preds maps body, info)

  (** substitution for term variable *)
  let rec subst maps = function
    | Atom (atom, info) -> Atom(Atom.subst maps atom, info)
    | UnaryOp(Neg, phi, info) -> UnaryOp(Neg, subst maps phi, info)
    | BinaryOp(op, phi1, phi2, info) -> BinaryOp(op, subst maps phi1, subst maps phi2, info)
    | Bind(binder, bounds, body, info) ->
      let maps =
        List.fold ~init:maps ~f:(fun maps (var, _) -> Map.Poly.remove maps var) bounds
      in
      Bind(binder, bounds, subst maps body, info)
    | LetRec(funcs, body, info) ->
      let funcs =
        List.map ~f:(fun (fix, pvar, arg_sorts, func_body) ->
            let maps =
              List.fold ~init:maps ~f:(fun maps (var, _) -> Map.Poly.remove maps var) arg_sorts
            in
            (fix, pvar, arg_sorts, subst maps func_body)) funcs in
      LetRec(funcs, subst maps body, info)

  let rec subst_pred ident params phi =
    function
    | Atom (atom, _) -> Atom.subst_pred ident params phi atom
    | UnaryOp(Neg, phi', info) ->
      UnaryOp(Neg, subst_pred ident params phi phi', info)
    | BinaryOp(op, phi1, phi2, info) ->
      BinaryOp(op, subst_pred ident params phi phi1, subst_pred ident params phi phi2, info)
    | Bind(binder, params', phi', info) ->
      let phi = subst_pred ident params phi phi' in
      Bind (binder, params', phi, info)
    | LetRec(bounded, body, info) ->
      (* ToDo: the following code is wrong if ident is bound by let rec *)
      let bounded = List.map ~f:(fun (fp, pvar, params', phi') -> (fp, pvar, params', subst_pred ident params phi phi')) bounded in
      let body = subst_pred ident params phi body in
      LetRec (bounded, body, info)

  let rec subst_preds maps = function
    | Atom (atom, _) -> Atom.subst_preds maps atom
    | UnaryOp(Neg, phi, info) ->
      UnaryOp (Neg, subst_preds maps phi, info)
    | BinaryOp(op, phi1, phi2, info) ->
      BinaryOp(op, subst_preds maps phi1, subst_preds maps phi2, info)
    | Bind(binder, params, phi, info) ->
      let phi = subst_preds maps phi in
      Bind (binder, params, phi, info)
    | LetRec(bounded, body, info) ->
      (* ToDo: the following code is wrong if ident is bound by let rec *)
      let bounded = List.map ~f:(fun (fp, pvar, params, phi) -> (fp, pvar, params, subst_preds maps phi)) bounded in
      let body = subst_preds maps body in
      LetRec (bounded, body, info)

  let rec replace_pred_ident from to_ = function
    | Atom (atom, info) -> Atom (Atom.replace_pred_ident from to_ atom, info)
    | UnaryOp (Neg, phi, info) ->
      let phi: Formula.t = replace_pred_ident from to_ phi in
      UnaryOp (Neg, phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, Formula.replace_pred_ident from to_ phi1, Formula.replace_pred_ident from to_ phi2, info)
    | Bind (_, _, _, _) -> failwith "not implemented" (* TODO *)
    | LetRec (bounded, body, info) ->
      let bounded = List.map ~f:(fun (fp, pvar, params, phi) ->
          if pvar = from then (fp, pvar, params, phi)
          else (fp, pvar, params, Formula.replace_pred_ident from to_ phi)
        ) bounded in
      let body = Formula.replace_pred_ident from to_ body in
      LetRec(bounded, body, info)

  let rec subst_neg pvar = function
    | Atom (Atom.App(Predicate.Var (pvar', sort), args, info), info') ->
      let atom = Atom.App(Predicate.Var (pvar', sort), args, info) in
      if pvar = pvar' then UnaryOp(Neg, Atom(atom, info), Dummy)
      else Atom(Atom.subst_neg pvar atom, info')
    | Atom (atom, info) -> Atom (Atom.subst_neg pvar atom, info)
    | UnaryOp(Neg, phi, info) ->
      (match subst_neg pvar phi with
       | UnaryOp(Neg, phi', _) -> phi'
       | phi' -> UnaryOp(Neg, phi', info))
    | BinaryOp(op, phi1, phi2, info) ->
      BinaryOp(op, subst_neg pvar phi1, subst_neg pvar phi2, info)
    | Bind(binder, bounds, body, info) ->
      Bind(binder, bounds, subst_neg pvar body, info)
    | LetRec(funcs, body, info) ->
      LetRec(List.map ~f:(fun (fix, pvar', bounds, body) -> fix, pvar', bounds, subst_neg pvar body) funcs,
             subst_neg pvar body, info)

  let rec subst_pvar maps fml = match fml with
    | Atom (Atom.App(Predicate.Var (pvar', sorts), args, _), _) ->
      if Core.Map.Poly.mem maps pvar' then (
        assert (sorts = [] && args = []);
        Core.Map.Poly.find_exn maps pvar'
      )
      else
        fml
    | Atom (Atom.True _, _) | Atom (Atom.False _, _) -> fml
    | UnaryOp(Neg, phi, info) ->
      UnaryOp(Neg, subst_pvar maps phi, info)
    | BinaryOp(op, phi1, phi2, info) ->
      BinaryOp(op, subst_pvar maps phi1, subst_pvar maps phi2, info)
    | Bind(binder, bounds, body, info) ->
      Bind(binder, bounds, subst_pvar maps body, info)
    | _ -> failwith "not implemented"

  (* aux *)
  let simplify_andor_norec op phi1 phi2 info =
    match (op, phi1, phi2) with
    | And, Atom (Atom.False info', info), _
    | And, _, Atom (Atom.False info', info)
      -> Atom (Atom.False info', info)

    | Or, Atom (Atom.True info', info), _
    | Or, _, Atom (Atom.True info', info)
      -> Atom(Atom.True info', info)

    | And, Atom (Atom.True _, _), phi
    | And, phi, Atom (Atom.True _, _)
    | Or, Atom (Atom.False _, _), phi
    | Or, phi, Atom (Atom.False _, _)
      -> phi
    | (op, phi1, phi2) -> BinaryOp(op, phi1, phi2, info)

  let flip_quantifier = function Forall -> Exists | Exists -> Forall

  let rec simplify = function
    | Atom (atom, info) -> Atom(Atom.simplify atom, info)
    | UnaryOp(Neg, phi, _) -> simplify_neg phi
    | BinaryOp(Imply, phi1, phi2, info) ->
      simplify (BinaryOp(Or, UnaryOp(Neg, phi1, Dummy), phi2, info))
    | BinaryOp(Iff, phi1, phi2, info) ->
      simplify (BinaryOp(And, BinaryOp(Imply, phi1, phi2, Dummy), BinaryOp(Imply, phi2, phi1, Dummy), info))
    | BinaryOp(op, phi1, phi2, info) -> begin
        let phi1 = simplify phi1 in
        let phi2 = simplify phi2 in
        simplify_andor_norec op phi1 phi2 info
      end
    | Bind(binder, bounds, phi, info) ->
      let phi = simplify phi in
      (match phi with
       | Bind(binder', bounds', phi', _) ->
         if binder' = binder then
           Bind(binder, bounds' @ bounds, phi', info)
         else
           Bind(binder, bounds, phi, info)
       | _ -> Bind(binder, bounds, phi, info))
    | LetRec(funcs, phi, info) ->
      LetRec(List.map ~f:(fun (fix, pvar, bounds, body) ->
          fix, pvar, bounds, simplify body
        ) funcs, simplify phi, info)

  and simplify_neg = function
    | Atom (Atom.App(Predicate.Var (var, sort), args, info), info')
      -> UnaryOp(Neg, Atom (Atom.App(Predicate.Var (var, sort), args, info), info'), Dummy)
    | Atom (atom, info) -> Atom(Atom.simplify_neg atom, info)
    | UnaryOp(Neg, phi, _) -> simplify phi
    | BinaryOp(Imply, phi1, phi2, info) ->
      simplify_neg (BinaryOp(Or, UnaryOp(Neg, phi1, Dummy), phi2, info))
    | BinaryOp(Iff, phi1, phi2, info) ->
      simplify_neg (BinaryOp(And, BinaryOp(Imply, phi1, phi2, Dummy), BinaryOp(Imply, phi2, phi1, Dummy), info))
    | BinaryOp(And, phi1, phi2, info) -> begin
        let phi1 = simplify_neg phi1 in
        let phi2 = simplify_neg phi2 in
        simplify_andor_norec Or phi1 phi2 info
      end
    | BinaryOp(Or, phi1, phi2, info) -> begin
        let phi1 = simplify_neg phi1 in
        let phi2 = simplify_neg phi2 in
        simplify_andor_norec And phi1 phi2 info
      end
    | Bind(binder, bounds, phi, info) ->
      let binder = flip_quantifier binder in
      let phi = simplify_neg phi in
      (match phi with
       | Bind(binder', bounds', phi', _) ->
         if binder' = binder then
           Bind(binder, bounds' @ bounds, phi', info)
         else
           Bind(binder, bounds, phi, info)
       | _ -> Bind(binder, bounds, phi, info))
    | LetRec(funcs, phi, info) ->
      let pvars = List.map ~f:(fun (_, pvar, _, _) -> pvar) funcs in
      LetRec(List.map ~f:(fun (fix, pvar, bounds, body) ->
          Predicate.flip_fixpoint fix, pvar, bounds,
          simplify_neg
          @@ List.fold_left ~f:(fun body pvar -> subst_neg pvar body) ~init:body pvars
        ) funcs,
             simplify_neg @@ List.fold_left ~f:(fun phi pvar -> subst_neg pvar phi) ~init:phi pvars,
             info)

  let rec get_ftv = function
    | UnaryOp(_, phi, _) -> get_ftv phi
    | BinaryOp(_, phi1, phi2, _) -> Set.Poly.union (get_ftv phi1) (get_ftv phi2)
    | Atom(atom, _) ->  Atom.get_ftv atom
    | Bind(_, bounds, phi, _) ->
      Set.Poly.diff (get_ftv phi) (bounds |> List.map ~f:fst |> Set.Poly.of_list)
    | LetRec(funcs, phi, _) ->
      (get_ftv phi :: List.map funcs ~f:(fun (_, _, bounds, body) ->
           Set.Poly.diff (get_ftv body)
             (bounds |> List.map ~f:fst |> Set.Poly.of_list)))
      |> Set.Poly.union_list

  let rec get_ftv_sort = function
    | UnaryOp(_, phi, _) -> get_ftv_sort phi
    | BinaryOp(_, phi1, phi2, _) -> Set.Poly.union (get_ftv_sort phi1) (get_ftv_sort phi2)
    | Atom(atom, _) ->  Atom.get_ftv_sort atom
    | Bind(_, bounds, phi, _) ->
      Set.Poly.diff (get_ftv_sort phi) (bounds |> Set.Poly.of_list)
    | LetRec(funcs, phi, _) ->
      (get_ftv_sort phi :: List.map funcs ~f:(fun (_, _, bounds, body) ->
           Set.Poly.diff (get_ftv_sort body)
             (bounds |> Set.Poly.of_list)))
      |> Set.Poly.union_list

  let rec get_fpv = function
    | UnaryOp(_, phi, _) -> get_fpv phi
    | BinaryOp(_, phi1, phi2, _) -> Set.Poly.union (get_fpv phi1) (get_fpv phi2)
    | Atom(atom, _) -> Atom.get_fpv atom
    | Bind(_, _, phi, _) -> get_fpv phi
    | LetRec(funcs, phi, _) ->
      Set.Poly.diff
        ((get_fpv phi :: List.map ~f:(fun (_, _, _, body) -> get_fpv body) funcs)
         |> Set.Poly.union_list)
        (funcs |> List.map ~f:(fun (_, pvar, _, _) -> pvar) |> Set.Poly.of_list)

  let rec refresh_pvar = function
    | Atom (atom, info) -> Atom (Atom.refresh_pvar atom, info)
    | UnaryOp(Neg, phi, info) -> UnaryOp (Neg, refresh_pvar phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, refresh_pvar phi1, refresh_pvar phi2, info)
    | Bind (binder, bounds, phi, info) ->
      Bind (binder, bounds, refresh_pvar phi, info)
    | LetRec(funcs, phi, info) ->
      let maps = List.map ~f:(fun (_, pvar, _, _) -> pvar, Ident.mk_fresh_pvar ()) funcs in
      let update phi = List.fold_left ~f:(fun acc (old, fresh) -> replace_pred_ident old fresh acc) ~init:phi maps in
      let funcs = List.mapi ~f:(fun index (fp, _, params, phi) ->
          let phi = update phi in
          match List.nth maps index with
          | None -> assert false
          | Some(_, pvar) -> (fp, pvar, params, phi)
        ) funcs
      in
      let phi = update phi in
      LetRec (funcs, phi, info)

  let rec extend_pred_params ident extended_params = function
    | Atom (atom, info) -> Atom (Atom.extend_pred_params ident extended_params atom, info)
    | UnaryOp (op, phi, info) -> UnaryOp (op, extend_pred_params ident extended_params phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, extend_pred_params ident extended_params phi1, extend_pred_params ident extended_params phi2, info)
    | Bind (binder, bounded, phi, info) ->
      Bind (binder, bounded, extend_pred_params ident extended_params phi, info)
    | LetRec (fps, body, info) ->
      let fps = List.map ~f:(fun (fp, pvar, params, body) -> fp, pvar, params, extend_pred_params ident extended_params body) fps in
      let body = extend_pred_params ident extended_params body in
      LetRec (fps, body, info)

  let rec refresh_tvar =
    function
    | Atom (atom, info) -> mk_atom (Atom.refresh_tvar atom) info
    | UnaryOp(Neg, phi, info) -> mk_neg (refresh_tvar phi) info
    | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, refresh_tvar phi1, refresh_tvar phi2, info)
    | Bind (binder, bounds, phi, info) ->
      let bounds' = List.map
          ~f:(fun (_, s) -> (Ident.mk_fresh_tvar(), s)) bounds in
      let map = List.zip_exn bounds bounds'
                |> List.map
                  ~f:(fun ((t,_), (t', s)) ->
                      (t, Term.mk_var t' s Dummy))
                |> Map.Poly.of_alist_exn in
      Bind (binder, bounds', subst map phi, info)
    | LetRec(funcs, body, info) ->
      let funcs' = List.map ~f:(fun (fp, pvar, params, body) ->
          Predicate.let_fix @@ Predicate.refresh_tvar @@ Predicate.Fixpoint (fp, pvar, params, body)
        ) funcs in
      let body' = refresh_tvar body in
      LetRec (funcs', body', info)

  let rec nesting_level =function
    | UnaryOp(_, phi, _) -> nesting_level phi
    | BinaryOp(_, phi1, phi2, _) ->
      max (nesting_level phi1) (nesting_level phi2)
    | Atom(atom, _) -> Atom.nesting_level atom
    | Bind(_, _, phi, _) -> nesting_level phi
    | LetRec (bounded, body, _) ->
      let levels = List.map ~f:(fun (_, _, _, phi) -> 1 + nesting_level phi) bounded in
      let levels = (nesting_level body) :: levels in
      List.fold_left ~f:(fun acc level -> if acc < level then level else acc) ~init:0 levels

  let rec number_of_quantifiers = function
    | UnaryOp(_, phi, _) -> number_of_quantifiers phi
    | BinaryOp(_, phi1, phi2, _) ->
      (number_of_quantifiers phi1) + (number_of_quantifiers phi2)
    | Atom(atom, _) -> Atom.number_of_quantifiers atom
    | Bind(_, _, phi, _) -> 1 + (number_of_quantifiers phi)
    | LetRec (bounded, body, _) ->
      let nums = List.map ~f:(fun (_, _, _, phi) -> number_of_quantifiers phi) bounded in
      let nums = (number_of_quantifiers body) :: nums in
      List.fold_left ~f:(fun acc num -> acc + num) ~init:0 nums

  let rec number_of_pvar_apps is_pos = function
    | Atom(atom, _) -> Atom.number_of_pvar_apps is_pos atom
    | UnaryOp(Neg, phi, _) -> number_of_pvar_apps (not is_pos) phi
    | BinaryOp(Imply, phi1, phi2, _) ->
      (number_of_pvar_apps (not is_pos) phi1) + (number_of_pvar_apps is_pos phi2)
    | BinaryOp(Iff, _, _, _) -> assert false
    | BinaryOp(And, phi1, phi2, _) | BinaryOp(Or, phi1, phi2, _) ->
      (number_of_pvar_apps is_pos phi1) + (number_of_pvar_apps is_pos phi2)
    | Bind(_, _, phi, _) -> number_of_pvar_apps is_pos phi
    | LetRec(_, _, _) -> assert false
  (*List.fold_left (fun acc (_, _, _, phi) -> acc + (number_of_pvar_apps is_pos phi))
    (number_of_pvar_apps is_pos body) bounded*)

  
  let rec classify eqrel = function
    | [] -> []
    | x :: xs ->
      let t, f = partition (eqrel x) xs in
      (x :: t) :: (classify eqrel f)
      
  let rec count_pvar_apps = function
    | Atom(atom, _) -> Atom.count_pvar_apps atom
    | UnaryOp(Neg, phi, _) -> List.Assoc.map (count_pvar_apps phi) ~f:(fun (pc, nc) -> nc, pc)
    | BinaryOp(Imply, phi1, phi2, _) ->
      let r1 = List.Assoc.map (count_pvar_apps phi1) ~f:(fun (pc, nc) -> nc, pc) in
      let r2 = count_pvar_apps phi2 in
      (r1 @ r2)
      |> classify (fun x y -> fst x = fst y)
      |> List.map ~f:(function [] -> assert false | (x :: xs) ->
          fst x,
          let pcs, ncs = List.unzip (snd x :: List.map ~f:snd xs) in
          (List.fold pcs ~init:0 ~f:(+), List.fold ncs ~init:0 ~f:(+))
        )
    | BinaryOp(Iff, _, _, _) -> assert false
    | BinaryOp(And, phi1, phi2, _) | BinaryOp(Or, phi1, phi2, _) ->
      let r1 = count_pvar_apps phi1 in
      let r2 = count_pvar_apps phi2 in
      (r1 @ r2)
      |> classify (fun x y -> fst x = fst y)
      |> List.map ~f:(function [] -> assert false | (x :: xs) ->
          fst x,
          let pcs, ncs = List.unzip (snd x :: List.map ~f:snd xs) in
          (List.fold pcs ~init:0 ~f:(+), List.fold ncs ~init:0 ~f:(+))
        )
    | Bind(_, _, phi, _) -> count_pvar_apps phi
    | LetRec(_, _, _) -> assert false

  let rec ast_size = function
    | UnaryOp(_, phi, _) -> 1 + (ast_size phi)
    | BinaryOp(_, phi1, phi2, _) -> 1 + (ast_size phi1) + (ast_size phi2)
    | Atom(atom, _) -> 1 + Atom.ast_size atom
    | Bind(_, _, phi, _) -> 1 + ast_size phi
    | LetRec (bounded, phi, _) ->
      (List.fold_left ~f:(fun acc (_, _, _, phi) -> acc + (ast_size phi)) ~init:1 bounded) + (ast_size phi)

  let rec atoms = function
    | UnaryOp(_, phi, _) -> atoms phi
    | BinaryOp(_, phi1, phi2, _) -> Set.Poly.union (atoms phi1) (atoms phi2)
    | Atom(atom, _) -> Set.Poly.singleton atom
    | Bind(_, _, phi, _) -> atoms phi
    | LetRec (bounded, body, _) ->
      (atoms body :: List.map ~f:(fun (_, _, _, phi) -> atoms phi) bounded)
      |> Set.Poly.union_list

  (* assume that phi is in nnf *)
  let rec cnf_of_aux = function
    | UnaryOp(Neg, phi, _) ->
      (match phi with
       | Atom(atom, _) ->
         if Atom.is_true atom then
           [[], [], []]
         else if Atom.is_false atom then
           []
         else if Atom.is_varapp atom then
           [[], [atom], []]
         else if Atom.is_symapp atom then
           [[], [], [mk_neg (mk_atom atom Dummy) Dummy]]
         else assert false
       | _ -> assert false)
    | BinaryOp(And, phi1, phi2, _) ->
      let cls1 = cnf_of_aux phi1 in
      let cls2 = cnf_of_aux phi2 in
      let phis, cls =
        List.partition_map
          (cls1 @ cls2)
          ~f:(fun (ps, ns, phis) ->
              if ps = [] && ns = [] then
                `Fst(or_of phis Dummy)
              else
                `Snd(ps, ns, phis))
      in
      if phis = [] then cls else ([], [], [and_of phis Dummy]) :: cls
    | BinaryOp(Or, phi1, phi2, _) ->
      let cls1 = cnf_of_aux phi1 in
      let cls2 = cnf_of_aux phi2 in
      List.map
        (List.cartesian_product cls1 cls2)
        ~f:(fun ((ps1, ns1, phis1), (ps2, ns2, phis2)) ->
            ps1 @ ps2,
            ns1 @ ns2,
            phis1 @ phis2)
    | BinaryOp(Imply, _, _, _) | BinaryOp(Iff, _, _, _) -> assert false
    | Atom(atom, _) ->
      if Atom.is_true atom then
        []
      else if Atom.is_false atom then
        [[], [], []]
      else if Atom.is_varapp atom then
        [[atom], [], []]
      else if Atom.is_symapp atom then
        [[], [], [mk_atom atom Dummy]]
      else assert false
    | Bind(_, _, _, _) as phi -> [[], [], [phi]]
    | LetRec (_, _, _) -> assert false
  (* cnf_of phi
      input  : Formula of NNF
      output : a list of clauses where a clause is represented by a triple (ps,ns,phi') consisting of predicate variable applications ps, negated predicate variable applications ns, and a pure formula *)
  let cnf_of phi =
    phi
    |> cnf_of_aux
    |> List.map ~f:(fun (ps, ns, phis) -> ps, ns, or_of phis Dummy)
  let of_clause (ps, ns, phi) =
    let phis =
      phi :: (List.map ~f:(fun a -> mk_atom a Dummy) ps @
              List.map ~f:(fun a -> mk_neg (mk_atom a Dummy) Dummy) ns)
    in
    or_of phis Dummy
  let of_cnf clauses = and_of (List.map ~f:of_clause clauses) Dummy

  let alpha_conv_clause (ps, ns, phi) =
    let map =
      (get_ftv phi :: List.map ps ~f:Atom.get_ftv @ List.map ns ~f:Atom.get_ftv)
      |> Set.Poly.union_list
      |> Set.Poly.to_list
      |> List.map ~f:(fun x -> (x, Ident.mk_fresh_tvar()))
      |> Map.Poly.of_alist_exn
    in
    List.map ~f:(Atom.rename map) ps,
    List.map ~f:(Atom.rename map) ns,
    rename map phi

  let str_of_unop = function | Neg -> "Neg"
  let str_of_binop = function | And -> "And" | Or -> "Or" | Imply -> "Imply" | Iff -> "Iff"
  let str_of_binder = function | Forall -> "Forall" | Exists -> "Exists"

  let rec str_of = function
    | Atom (atom, _) -> Printf.sprintf "Atom (%s)" @@ Atom.str_of atom
    | UnaryOp (op, phi, _) -> Printf.sprintf "UnaryOp (%s, %s)" (str_of_unop op) (str_of phi)
    | BinaryOp (op, phi1, phi2, _) ->
      Printf.sprintf "BinaryOp(%s, %s, %s)" (str_of_binop op) (str_of phi1) (str_of phi2)
    | Bind (binder, terms, phi, _) ->
      Printf.sprintf "Bind (%s, %s, %s)" (str_of_binder binder)
        (List.fold_left ~f:(fun acc (Ident.Tvar id, _) -> acc ^ ", " ^ id) ~init:"" terms) (str_of phi)
    | LetRec (_, phi, _) ->
      (* TODO: implements *)
      Printf.sprintf "LetRec (fixpoints, %s)" @@ str_of phi
end

and T_bool : sig
  type fun_sym += Bool of Atom.t | Formula of Formula.t | IfThenElse
  type pred_sym += Eq | Neq
  type Sort.t += SBool

  (** constructor *)
  val mk_bool: Atom.t -> info -> Term.t
  val mk_formula : Formula.t -> info -> Term.t
  val mk_if_then_else : Term.t -> Term.t -> Term.t -> info -> Term.t
  val mk_eq: Term.t -> Term.t -> info -> Atom.t
  val mk_neq: Term.t -> Term.t -> info -> Atom.t
end = struct
  type fun_sym += Bool of Atom.t | Formula of Formula.t | IfThenElse
  type pred_sym += Eq | Neq
  type Sort.t += SBool

  (** constructor *)
  let mk_bool atom info = Term.mk_funapp (Bool atom) [] info
  let mk_formula phi info = Term.mk_funapp (Formula phi) [] info
  let mk_if_then_else cond then_ else_ info = Term.mk_funapp IfThenElse [cond; then_; else_] info
  let mk_eq t1 t2 info = Atom.mk_app (Predicate.Psym Eq) [t1; t2] info
  let mk_neq t1 t2 info = Atom.mk_app (Predicate.Psym Neq) [t1; t2] info
end

(* TODO: refactoring
   divide into T_arithmetic.Integer nad T_arithmetic.Real
*)
and T_int : sig
  type fun_sym +=
    | Int of Bigint.t | Real of string
    | Add | Sub | Mult | Div | Mod | UnaryNeg
  type pred_sym += Leq | Geq | Lt | Gt
  type Sort.t += SInt | SReal | SRefInt | SUnrefInt

  (** constructor *)
  val zero: info -> Term.t
  val one: info -> Term.t
  val hundred: info -> Term.t
  val mk_int: Bigint.t -> info -> Term.t
  val mk_from_int: int -> info -> Term.t
  val mk_real: string -> info -> Term.t
  val mk_add: Term.t -> Term.t -> info -> Term.t
  val mk_sub: Term.t -> Term.t -> info -> Term.t
  val mk_mult: Term.t -> Term.t -> info -> Term.t
  val mk_div: Term.t -> Term.t -> info -> Term.t
  val mk_mod: Term.t -> Term.t -> info -> Term.t
  val mk_unary_neg: Term.t -> info -> Term.t

  val mk_neg: Term.t -> info -> Term.t

  val mk_sum: Term.t list -> Term.t -> info -> Term.t

  val mk_leq: Term.t -> Term.t -> info -> Atom.t
  val mk_geq: Term.t -> Term.t -> info -> Atom.t
  val mk_lt: Term.t -> Term.t -> info -> Atom.t
  val mk_gt: Term.t -> Term.t -> info -> Atom.t

  (** test *)
  val is_int: Term.t -> bool
  val is_real: Term.t -> bool
  val is_add: Term.t -> bool
  val is_sub: Term.t -> bool
  val is_mult: Term.t -> bool
  val is_div: Term.t -> bool
  val is_mod: Term.t -> bool
  val is_unary_neg: Term.t -> bool

  val is_leq: Atom.t -> bool
  val is_geq: Atom.t -> bool
  val is_lt: Atom.t -> bool
  val is_gt: Atom.t -> bool

  (** destructor *)
  val let_int: Term.t -> Bigint.t
  val let_real: Term.t -> string
  val let_add: Term.t -> Term.t * Term.t * info
  val let_sub: Term.t -> Term.t * Term.t * info
  val let_mult: Term.t -> Term.t * Term.t * info
  val let_div: Term.t -> Term.t * Term.t * info
  val let_mod: Term.t -> Term.t * Term.t * info
  val let_unary_neg: Term.t -> Term.t * info

  val let_leq: Atom.t -> Term.t * Term.t * info
  val let_geq: Atom.t -> Term.t * Term.t * info
  val let_lt: Atom.t -> Term.t * Term.t * info
  val let_gt: Atom.t -> Term.t * Term.t * info

  val binfun_of_fsym: fun_sym -> Bigint.t -> Bigint.t -> Bigint.t
  val binfun_of_psym: pred_sym -> Bigint.t -> Bigint.t -> bool

end = struct
  type fun_sym +=
    | Int of Bigint.t | Real of string
    | Add | Sub | Mult | Div | Mod | UnaryNeg
  type pred_sym += Leq | Geq | Lt | Gt
  type Sort.t += SInt | SReal | SRefInt | SUnrefInt

  (** constructor *)
  let zero info = Term.mk_funapp (Int (Bigint.of_int 0)) [] info
  let one info = Term.mk_funapp (Int (Bigint.of_int 1)) [] info
  let hundred info = Term.mk_funapp (Int (Bigint.of_int 100)) [] info
  let mk_int n = Term.mk_funapp (Int n) []
  let mk_from_int n = Term.mk_funapp (Int (Bigint.of_int n)) []
  let mk_real f = Term.mk_funapp (Real f) []
  let mk_add t1 t2 = Term.mk_funapp Add [t1; t2]
  let mk_sub t1 t2 = Term.mk_funapp Sub [t1; t2]
  let mk_mult t1 t2 = Term.mk_funapp Mult [t1; t2]
  let mk_div t1 t2 = Term.mk_funapp Div [t1; t2]
  let mk_mod t1 t2 = Term.mk_funapp Mod [t1; t2]
  let mk_unary_neg t = Term.mk_funapp UnaryNeg [t]

  let mk_neg t info =
    mk_mult (mk_int (Bigint.neg(Bigint.one)) info) t info

  let mk_sum ts c info =
    List.fold_left ~f:(fun acc ax -> mk_add ax acc info) ~init:c ts

  let mk_leq t1 t2 = Atom.mk_app (Predicate.Psym Leq) [t1; t2]
  let mk_geq t1 t2 = Atom.mk_app (Predicate.Psym Geq) [t1; t2]
  let mk_lt t1 t2 = Atom.mk_app (Predicate.Psym Lt) [t1; t2]
  let mk_gt t1 t2 = Atom.mk_app (Predicate.Psym Gt) [t1; t2]

  (** test *)
  let is_int = function Term.FunApp(Int _, [], _) -> true | _ -> false
  let is_real = function Term.FunApp(Real _, [], _) -> true | _ -> false
  let is_add = function Term.FunApp(Add, _, _) -> true | _ -> false
  let is_sub = function Term.FunApp(Sub, _, _) -> true | _ -> false
  let is_mult = function Term.FunApp(Mult, _, _) -> true | _ -> false
  let is_div = function Term.FunApp(Div, _, _) -> true | _ -> false
  let is_mod = function Term.FunApp(Mod, _, _) -> true | _ -> false
  let is_unary_neg = function Term.FunApp(UnaryNeg, _, _) -> true | _ -> false

  let psym_of_atom = function
    | Atom.App(Predicate.Psym sym, _, _) -> sym
    | _ -> assert false
  let is_leq atom = Leq = psym_of_atom atom
  let is_geq atom = Geq = psym_of_atom atom
  let is_lt atom = Lt = psym_of_atom atom
  let is_gt atom = Gt = psym_of_atom atom

  (** destructor *)
  let let_int = function
    | Term.FunApp(Int n, [], _) -> n
    | _ -> assert false
  let let_real = function
    | Term.FunApp (Real f, [], _) -> f
    | _ -> assert false
  let let_add = function
    | Term.FunApp(Add, [phi1; phi2], info) -> phi1, phi2, info
    | _ -> assert false
  let let_sub = function
    | Term.FunApp(Sub, [phi1; phi2], info) -> phi1, phi2, info
    | _ -> assert false
  let let_mult = function
    | Term.FunApp(Mult, [phi1; phi2], info) -> phi1, phi2, info
    | _ -> assert false
  let let_div = function
    | Term.FunApp(Div, [phi1; phi2], info) -> phi1, phi2, info
    | _ -> assert false
  let let_mod = function
    | Term.FunApp(Mod, [phi1; phi2], info) -> phi1, phi2, info
    | _ -> assert false
  let let_unary_neg = function
    | Term.FunApp(UnaryNeg, [t], info) -> t, info
    | _ -> assert false

  let let_leq = function
    | Atom.App(Predicate.Psym Leq, [t1; t2], info) -> t1, t2 , info
    | _ -> assert false
  let let_geq = function
    | Atom.App(Predicate.Psym Geq, [t1; t2], info) -> t1, t2, info
    | _ -> assert false
  let let_lt = function
    | Atom.App(Predicate.Psym Lt, [t1; t2], info) -> t1, t2, info
    | _ -> assert false
  let let_gt = function
    | Atom.App(Predicate.Psym Gt, [t1; t2], info) -> t1, t2, info
    | _ -> assert false

  let binfun_of_psym = function
    | Gt -> Bigint.(>)
    | Lt -> Bigint.(<)
    | Geq -> Bigint.(>=)
    | Leq -> Bigint.(<=)
    | T_bool.Eq -> Bigint.(=)
    | T_bool.Neq -> Bigint.(<>)
    | _ -> assert false

  let binfun_of_fsym = function
    | Add -> Bigint.(+)
    | Sub -> Bigint.(-)
    | Mult -> Bigint.( * )
    | Div -> Bigint.(/)
    | Mod -> Bigint.(%)
    | _ -> assert false
end

and AstUtil : sig
  val sort_of_term : (Ident.tvar, Sort.t) Env.t -> Term.t -> Sort.t
  val sorts_of_params : (Ident.tvar * Sort.t) list -> Sort.t list
  val args_of_params : (Ident.tvar * Sort.t) list -> Term.t list
end = struct
  let rec sort_of_term env = function
    | Term.Var(_, sort, _) -> sort
    | Term.FunApp (T_int.Int _, _, _) | Term.FunApp (T_int.Mod, _, _) ->
      T_int.SInt
    | Term.FunApp (T_int.Real _, _, _) ->
      T_int.SReal
    | Term.FunApp(T_int.Add, [t; _], _) | Term.FunApp(T_int.Sub, [t; _], _)
    | Term.FunApp(T_int.Mult, [t; _], _) | Term.FunApp(T_int.Div, [t; _], _)
    | Term.FunApp(T_int.UnaryNeg, [t; _], _) ->
      sort_of_term env t
    | _ -> assert false

  let sorts_of_params = List.map ~f:(fun (_, sort) -> sort)

  let args_of_params = List.map ~f:(fun (ident, sort) ->
      Term.mk_var ident sort Dummy)
end

