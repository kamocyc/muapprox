open Hflmc2_syntax
module Env = Env_no_value
(* open Hflz *)

type 'ty tarith = 'ty Id.t Arith.gen_t
[@@deriving eq,ord,show]

type partial_flag = UnkLabel of unit Id.t | Boundary | InBlock
[@@deriving eq,ord,show]

type ('ty, 'pflag) thflz =
  | Bool   of bool
  | Var    of 'ty Id.t
  | Or     of ('ty, 'pflag) thflz * ('ty, 'pflag) thflz
  | And    of ('ty, 'pflag) thflz * ('ty, 'pflag) thflz
  | Abs    of 'pflag * 'ty Id.t * ('ty, 'pflag) thflz
  | Forall of 'ty Id.t * ('ty, 'pflag) thflz
  | Exists of 'ty Id.t * ('ty, 'pflag) thflz
  | App    of ('ty, 'pflag) thflz * ('ty, 'pflag) thflz
  | Arith  of 'ty tarith
  | Pred   of Formula.pred * 'ty tarith list
  [@@deriving eq,ord,show]

type 'pflag ptype = TInt | TBool | TFunc of 'pflag * 'pflag ptype * 'pflag ptype | TVar of unit Hflmc2_syntax.Id.t
[@@deriving eq,ord,show]

type p_ptype = partial_flag ptype
type p_thflz = (p_ptype, partial_flag) thflz

type ('a, 'pflag) thes_rule = ('a Id.t * 'a Id.t list * ('a, 'pflag) thflz * Fixpoint.t)
[@@deriving eq,ord,show]

type s_thes_rules = (partial_flag ptype, partial_flag) thes_rule list
[@@deriving eq,ord,show]

let pp_partial_flag ?(with_id=false) ppf = function
  | UnkLabel id -> Fmt.pf ppf "_%s" (if with_id then Id.to_string id else "")
  | InBlock -> Fmt.pf ppf "_"
  | Boundary -> Fmt.pf ppf "|"

let show_partial_flag ?with_id =
  Hflmc2_util.fmt_string (pp_partial_flag ?with_id)

type insert_flag = Insert | NoInsert
[@@deriving eq,ord,show]

let pp_insert_flag ppf = function
  | Insert -> Fmt.pf ppf "i"
  | NoInsert -> Fmt.pf ppf "_"

let rec eq_p_type_except_flag t1 t2 = match t1, t2 with
  | TInt, TInt -> true
  | TBool, TBool -> true
  | TVar _, TVar _ -> true
  | TFunc (_, ty1, ty2), TFunc (_, ty1', ty2') ->
    (eq_p_type_except_flag ty1 ty1') && (eq_p_type_except_flag ty2 ty2')
  | _ -> false

module Print = struct
  include Print
  
  let rec pp_ptype_ : (formatter -> 'p -> unit) -> Prec.t -> 'p ptype Fmt.t =
    fun partial_flag prec ppf ty -> match ty with
        | TInt ->
          Fmt.pf ppf "int"
        | TBool ->
          Fmt.pf ppf "bool"
        | TVar id ->
          Fmt.pf ppf "var[%s]" (Id.to_string id)
        | TFunc (flag, p1, p2) ->
              show_paren (prec > Prec.arrow) ppf "@[<1>%a-%a->%a@]"
                (pp_ptype_ partial_flag Prec.(succ arrow)) p1
                partial_flag flag
                (pp_ptype_ partial_flag Prec.arrow) p2

  let pp_ptype pf = pp_ptype_ pf Prec.zero

  let arith prec ppf a = gen_arith_ (ignore_prec id) prec ppf a
  
  let formula ppf f = gen_formula_ void_ (ignore_prec id) Prec.zero ppf f
  
  let rec hflz_: (formatter -> 'ty -> unit) -> (formatter -> 'b -> unit) -> prec -> formatter -> ('ty, 'b) thflz -> unit
    = fun pty pf prec ppf phi ->
      match phi with
      | Bool true -> Fmt.string ppf "true"
      | Bool false -> Fmt.string ppf "false"
      (* | Var x -> Fmt.pf ppf "(%a :%a)" id x (format_ty_ Prec.zero) x.ty *)
      | Var x -> Fmt.pf ppf "%a" id x
      | Or(phi1,phi2)  ->
          show_paren (prec > Prec.or_) ppf "@[<hv 0>%a@ || %a@]"
            (hflz_ pty pf Prec.or_) phi1
            (hflz_ pty pf Prec.or_) phi2
      | And (phi1,phi2)  ->
          show_paren (prec > Prec.and_) ppf "@[<hv 0>%a@ && %a@]"
            (hflz_ pty pf Prec.and_) phi1
            (hflz_ pty pf Prec.and_) phi2
      | Abs (l, x, psi) ->
          show_paren (prec > Prec.abs) ppf "@[<1>λ[%a]%a:%a.@,%a@]"
            pf l
            id x
            pty x.ty
            (hflz_ pty pf Prec.abs) psi
      | Forall (x, psi) ->
          show_paren (prec > Prec.abs) ppf "@[<1>∀%a.@,%a@]"
            id x
            (hflz_ pty pf Prec.abs) psi
      | Exists (x, psi) ->
          show_paren (prec > Prec.abs) ppf "@[<1>∃%a.@,%a@]"
            id x
            (hflz_ pty pf Prec.abs) psi
      | App (psi1, psi2) ->
          show_paren (prec > Prec.app) ppf "@[<1>%a@ %a@]"
            (hflz_ pty pf Prec.app) psi1
            (hflz_ pty pf Prec.(succ app)) psi2
      | Arith a -> arith prec ppf a
      | Pred (pred, as') ->
          show_paren (prec > Prec.eq) ppf "%a"
            formula (Formula.Pred(pred, as'))

  let hflz : (formatter -> 'ty -> unit) -> (formatter -> 'b -> unit) -> ('ty, 'b) thflz Fmt.t =
    fun ty pf -> hflz_ ty pf Prec.zero

  let hflz_hes_rule : (formatter -> 'ty -> unit) -> (formatter -> 'b -> unit) -> ('ty, 'b) thes_rule Fmt.t =
    fun ty pf ppf (var, args, body, fix) ->
      Fmt.pf ppf "@[<2>%s %s : %a =%a@ %a@]"
        (Id.to_string var)
        (List.map (fun a -> Id.to_string a) args |> String.concat " ")
        ty var.ty
        fixpoint fix
        (hflz ty pf) body

  let hflz_hes : (formatter -> 'ty -> unit) -> (formatter -> 'b -> unit) -> ('ty, 'b) thes_rule list Fmt.t =
    fun ty pf ppf rules ->
      Fmt.pf ppf "@[<v>%a@]"
        (Fmt.list (hflz_hes_rule ty pf)) rules
end

let show_p_hflz = Hflmc2_util.fmt_string (Print.hflz (Print.pp_ptype pp_partial_flag) pp_partial_flag)
let show_p_ptype = Hflmc2_util.fmt_string (Print.pp_ptype pp_partial_flag)
let show_i_ptype = Hflmc2_util.fmt_string (Print.pp_ptype pp_insert_flag)

type i_ptype = insert_flag ptype
type i_thflz = (i_ptype, insert_flag) thflz
type i_thflz_rule = { var : i_ptype Id.t; body : i_thflz; fix : Fixpoint.t }

let pp_i_thflz ppf body =
  Fmt.pf ppf "%a"
  (Print.hflz (Print.pp_ptype pp_insert_flag) pp_insert_flag) body
  
let pp_i_thflz_rule ppf { var; body; fix } =
  Fmt.pf ppf "@[<2>%s =%a@ %a@]"
    (Id.to_string var)
    Print.fixpoint fix
    pp_i_thflz body

let pp_i_thflz_hes ppf rules =
  Fmt.pf ppf "@[<v>%a@]"
    (Fmt.list pp_i_thflz_rule) rules
        
let show_i_hflz_hes hes =
  Hflmc2_util.fmt_string pp_i_thflz_hes hes
let show_p_hflz_hes =
  Hflmc2_util.fmt_string (Print.hflz_hes (Print.pp_ptype pp_partial_flag) pp_partial_flag)

let rec subst_ptype ptype subst =
  match ptype with
  | TVar id -> begin
    match List.find_opt (fun (k, _) -> Id.eq k id) subst with
    | Some (_, v) -> v
    | None -> TVar id
  end
  | TInt | TBool -> ptype
  | TFunc (f, p1, p2) -> TFunc (f, subst_ptype p1 subst, subst_ptype p2 subst)

let is_occur id ty =
  let rec go (ty : p_ptype) = match ty with
    | TVar v -> Id.eq v id
    | TInt | TBool -> false
    | TFunc (_, p1, p2) -> go p1 || go p2 in
  go ty

let compose_subst (id, ty) subst =
  let ty' = subst_ptype ty subst in
  (id, ty') :: subst

let subst_label l subst = match l with
  | UnkLabel lid -> begin
    match List.find_opt (fun (k, _) -> Id.eq k lid) subst with
    | Some (_, v) -> v
    | None -> l
  end
  | _ -> l
  
let subst_labels (xs : (partial_flag * partial_flag) list) subst =
  List.map (fun (l1, l2) -> (subst_label l1 [subst], subst_label l2 [subst])) xs
  
let compose_subst_labels (lid, lab) (subst : (unit Id.t * partial_flag) list) =
  let lab = subst_label lab subst in
  (lid, lab) :: subst
  
let unify_labels (labels : (partial_flag * partial_flag) list) =
  let rec unify labels = match labels with
    | [] -> []
    | (f1', f2')::xs -> begin
      match f1', f2' with
      | UnkLabel l1, f2 ->
        compose_subst_labels (l1, f2) (unify (subst_labels xs (l1, f2))) 
      | f1, UnkLabel l2 ->
        compose_subst_labels (l2, f1) (unify (subst_labels xs (l2, f1)))
      | _ when f1' = f2' -> unify xs
      | _ -> failwith "unify_labels"
    end
  in
  (* print_endline "unify_labels";
  print_endline @@ Hflmc2_util.show_pairs (show_partial_flag ~with_id:true) (show_partial_flag ~with_id:true) labels; *)
  unify labels

let rec subst_label_on_ptype ty (target_id, value) =
  match ty with
  | TVar _ | TInt | TBool -> ty
  | TFunc (l, ty1, ty2) -> begin
    let l =
      match l with
      | UnkLabel id when id = target_id -> value
      | _ -> l in
    TFunc (
      l,
      subst_label_on_ptype ty1 (target_id, value),
      subst_label_on_ptype ty2 (target_id, value)
    )
  end
  
let subst_label_on_ptypes
    (r : (unit Id.t * p_ptype) list)
    (lab : (unit Id.t * partial_flag) list) =
  List.map
    (fun (id, ty) ->
      (
        id,
        List.fold_left
          (fun ty subst -> subst_label_on_ptype ty subst)
          ty
          lab
      )
    )
    r

let unify (constraints : (p_ptype * p_ptype) list) =
  let is_equal_ptype = (=) in
  let subst xs pair = List.map (fun (p1, p2) -> (subst_ptype p1 [pair], subst_ptype p2 [pair])) xs in
  let rec unify constraints = match constraints with
    | [] -> [], []
    | (t1, t2)::xs -> begin
      if is_equal_ptype t1 t2
      then unify xs
      else begin
        (* print_endline "unify2";
        print_endline @@ Hflmc2_util.show_pairs show_p_ptype show_p_ptype (constraints); *)
        match t1, t2 with
        | TFunc (l1, t11, t12), TFunc (l2, t21, t22) -> begin
          let ty, lab' = unify ((t11, t21) :: (t12, t22) :: xs) in
          ty, ((l1, l2) :: lab')
        end
        | TVar t11, t2 -> begin
          if is_occur t11 t2 then failwith "occur1";
          let ty, lab = unify (subst xs (t11, t2)) in
          compose_subst (t11, t2) ty, lab
        end
        | t1, TVar t21 -> begin
          if is_occur t21 t1 then failwith "occur2";
          let ty, lab = unify (subst xs (t21, t1)) in
          compose_subst (t21, t1) ty, lab
        end
        | _ ->
          failwith @@ "unify (left: " ^ show_p_ptype t1 ^ " / right: " ^ show_p_ptype t2 ^ ")"
      end
    end in
  (* print_endline "constraints:";
  print_endline @@ (Hflmc2_util.show_pairs show_p_ptype show_p_ptype constraints); *)
  
  let r, lab = unify constraints in
  (* print_endline "unified:";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_p_ptype r); *)
  
  let lab = unify_labels lab in
  (* print_endline "unified labels:";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_partial_flag lab); *)
  
  let r = subst_label_on_ptypes r lab in
  (* print_endline "unified (2):";
  print_endline @@ (Hflmc2_util.show_pairs Id.to_string show_p_ptype r); *)
  
  r, lab

let to_thflzs hes =
  let rec go env (phi : 'a Hflz.t): p_thflz = match phi with
    | Bool b -> Bool b
    | Var v ->
      let id = Env.lookup v env in
      Var id
    | Or (p1, p2) ->
      Or (go env p1, go env p2)
    | And (p1, p2) ->
      And (go env p1, go env p2)
    | Abs (x, p) ->
      let x = {x with Id.ty = TVar (Id.gen ())} in
      Abs (UnkLabel (Id.gen ()), x, go (Env.update [x] env) p)
    | Forall (x, p) ->
      let x = {x with Id.ty = TVar (Id.gen ())} in
      Forall (x, go (Env.update [x] env) p)
    | Exists (x, p) ->
      let x = {x with Id.ty = TVar (Id.gen ())} in
      Exists (x, go (Env.update [x] env) p)
    | App (p1, p2) ->
      App (go env p1, go env p2)
    | Arith a ->
      Arith (go_arith env a)
    | Pred (e, ps) ->
      Pred (e, List.map (go_arith env) ps)
  and go_arith env phi = match phi with
    | Int i -> Int i
    | Var v ->
      let id = Env.lookup v env in
      Var id
    | Op (e, ps) ->
      Op (e, List.map (go_arith env) ps)
  in
  let rules =
    List.map
      (fun {Hflz.var; body; fix} ->
        let args, body = Hflz.decompose_abs body in
        let args = List.map (fun arg -> { arg with Id.ty = TVar (Id.gen ())}) args in
        let rec go base ls = match ls with
          | [] -> base
          | x::xs -> TFunc (UnkLabel (Id.gen ()), x.Id.ty, go base xs)
        in 
        ( {var with ty = go TBool args}, args, body, fix )
      )
      hes in
  let global_env = List.map (fun (v, _, _, _) -> v) rules |> Env.create in
  List.map
    (fun (var, args, body, fix) ->
      let body = go (Env.update args global_env) body in
      ( var, args, body, fix )
    )
    rules

let generate_constraints (rules : s_thes_rules) : (p_ptype * p_ptype) list =
  let rec gen (env : p_ptype Env.t) (raw : p_thflz)
      : p_ptype * (p_ptype * p_ptype) list = match raw with
    | Bool _ -> (TBool, [])
    | Var v ->
      let id = Env.lookup v env in
      (id.ty, [])
    | Or (p1, p2) ->
      let t1, c1 = gen env p1 in
      let t2, c2 = gen env p2 in
      (TBool, (TBool, t1) :: (TBool, t2) :: c1 @ c2)
    | And (p1, p2) ->
      let t1, c1 = gen env p1 in
      let t2, c2 = gen env p2 in
      (TBool, (TBool, t1) :: (TBool, t2) :: c1 @ c2)
    | Abs (l, arg, body) ->
      let t, c = gen (Env.update [arg] env) body in
      (TFunc (l, arg.Id.ty, t), c)
    | Forall (arg, body) ->
      let t, c = gen (Env.update [arg] env) body in
      (t, (arg.Id.ty, TInt) :: c)
    | Exists (arg, body) ->
      let t, c = gen (Env.update [arg] env) body in
      (t, (arg.Id.ty, TInt) :: c)
    | App _ -> begin
      let rec go_app raw acc = match raw with
        | App (p1, p2) -> go_app p1 (p2::acc)
        | _ -> raw, List.rev acc
      in
      let lhs, args = go_app raw [] in
      let lhs_t, lhs_c = gen env lhs in
      let arg_ts, arg_cs = List.map (fun arg ->  gen env arg) args |> List.split in
      let return_tvar = Id.gen () in
      (* 最後の引数は、適用の切れ目。それ以外はまだ不明なので変数とする *)
      let rec mk_funt = function
        | a::a'::args -> TFunc (UnkLabel (Id.gen ()), a, mk_funt (a'::args))
        | [a] -> TFunc (Boundary, a, TVar return_tvar)
        | [] -> assert false
      in
      let rhs_t = mk_funt (List.rev arg_ts) in
      (TVar return_tvar, (lhs_t, rhs_t) :: lhs_c @ List.flatten arg_cs)
    end
    | Arith a ->
      let ty, c = gen_arith env a in
      (TInt, (TInt, ty) :: c)
    | Pred (_, ps) ->
      let results = List.map (gen_arith env) ps in
      let tys, cs = List.split results in
      (TBool, (List.map (fun ty -> (TInt, ty)) tys) @ (List.flatten cs))
  and gen_arith (env : p_ptype Env.t) (raw : p_ptype tarith)
      : p_ptype * (p_ptype * p_ptype) list = match raw with
    | Var v ->
      let id = Env.lookup v env in
      (id.ty, [(id.ty, TInt)])
    | Int _ -> (TInt, [])
    | Op (_, ps) ->
      let results = List.map (gen_arith env) ps in
      let tys, cs = List.split results in
      (TInt, (List.map (fun ty -> (TInt, ty)) tys) @ (List.flatten cs))
    in
  let global_env = List.map (fun (v, _, _, _) -> v) rules in
  let constraints =
    List.map
      (fun ( _var, args, body, _fix ) ->
        gen (Env.update args (Env.create global_env)) body |> snd
      )
      rules
    |> List.flatten in
  constraints

(* これをやると型が合わない *)
(* let rec subst_remaining_varty_to_bool ty =
  match ty with
  | TVar _ -> TBool
  | TInt -> TInt
  | TFunc (l, ty1, ty2) -> TFunc (l, subst_remaining_varty_to_bool ty1, subst_remaining_varty_to_bool ty2)
  | TBool -> TBool *)

let subst_program (rules : s_thes_rules) (subst : (unit Id.t * p_ptype) list) lab =
  let subst_ptype ty =
    List.fold_left
      (fun ty subst -> subst_label_on_ptype ty subst)
      (subst_ptype ty subst (* |> subst_remaining_varty_to_bool *))
      lab
    in
  let rec go (phi : p_thflz) = match phi with
    | Bool b -> Bool b
    | Var v -> Var { v with ty = subst_ptype v.ty }
    | Or (p1, p2) -> Or (go p1, go p2)
    | And (p1, p2) -> And (go p1, go p2)
    | Abs (l, v, p) -> begin
      let l = subst_label l lab in
      (* let l =
        match l with
        | UnkLabel _ -> begin
          match p with
          | Abs _ -> l
          | _ -> Boundary
        end
        | _ -> l in *)
      Abs (l, { v with Id.ty = subst_ptype v.Id.ty }, go p)
    end
    | Forall (v, p) -> Forall ({ v with Id.ty = subst_ptype v.Id.ty }, go p)
    | Exists (v, p) -> Exists ({ v with Id.ty = subst_ptype v.Id.ty }, go p)
    | App (p1, p2) -> App (go p1, go p2)
    | Arith a -> Arith (go_arith a)
    | Pred (op, ps) -> Pred (op, List.map go_arith ps)
  and go_arith (phi : p_ptype tarith) = match phi with
    | Int i -> Int i
    | Var v -> Var { v with ty = subst_ptype v.ty }
    | Op (e, ps) -> Op (e, List.map go_arith ps)
  in
  List.map (fun (var, args, body, fix) ->
    let var = { var with Id.ty = subst_ptype var.Id.ty } in
    let args = List.map (fun v -> { v with Id.ty = subst_ptype v.Id.ty }) args in
    let body = go body in
    (* print_endline @@ Id.to_string var;
    print_endline @@ show_p_ptype var.ty; *)
    ( var, args, body, fix )
  ) rules

let infer_thflz_type (rules : s_thes_rules): s_thes_rules =
  let constraints = generate_constraints rules in
  let substitution, lab = unify constraints in
  let rules = subst_program rules substitution lab in
  rules

let get_thflz_type (phi : ('a ptype, 'a) thflz) =
  let rec go (phi: ('a ptype, 'a) thflz) = match phi with
    | Bool _   -> TBool
    | Var v    -> v.ty
    | Or (f1, f2)  -> begin
      assert ((go f1) = TBool);
      assert ((go f2) = TBool);
      TBool
    end
    | And (f1, f2) -> begin
      assert ((go f1) = TBool);
      assert ((go f2) = TBool);
      TBool
    end
    | Abs (l, x, phi) -> TFunc (l, x.ty, go phi)
    | Forall (_, f1) -> begin
      assert ((go f1) = TBool);
      TBool
    end
    | Exists (_, f1) -> begin
      assert ((go f1) = TBool);
      TBool
    end
    | App (f1, f2) -> begin
      let ty1 = go f1 in
      match ty1 with
      | TFunc (_, a, b) -> begin
        (match a with
        | TInt -> (match f2 with Arith _ -> () | _ -> assert false)
        | _ -> begin
          let sty = go f2 in
          if not @@ eq_p_type_except_flag sty a then begin
            (* print_endline "phi";
            print_endline @@
              Hflmc2_util.fmt_string (Print.hflz (Print.pp_ptype (fun _ _ -> ())) (fun _ _ -> ())) phi;
            print_endline "sty";
            print_endline @@
              Hflmc2_util.fmt_string (Print.pp_ptype (fun _ _ -> ())) sty;
            print_endline "a";
            print_endline @@
              Hflmc2_util.fmt_string (Print.pp_ptype (fun _ _ -> ())) a; *)
            assert false
          end
        end);
        b
      end
      | _ -> failwith "Illegal type (Arith)"
    end
    | Pred _ -> TBool
    | Arith _ -> failwith "Illegal type (Arith)"
  in
  go phi

let rec border_to_insert_ty ty =
  match ty with
  | TInt -> TInt
  | _ -> begin
    let rec decompose_fun_ty ty = match ty with
      | TFunc (l, p1, p2) ->
        let args, body = decompose_fun_ty p2 in
        (l, p1)::args, body
      | _ -> [], ty
    in
    let rec compose_fun_ty tys body = match tys with
      | [] -> body
      | (l, ty)::xs -> TFunc (l, ty, compose_fun_ty xs body)
    in
    let is_ho arg = match arg with
      | TFunc _ -> true
      | _ -> false
    in
    let args, body = decompose_fun_ty ty in
    (* print_endline "border_to_insert_ty (before)";
    print_endline @@ show_p_ptype ty; *)
    assert (body = TBool);
    (* the last arrow type is Boundary, so ignore acc *)
    let args_s, _ =
      List.fold_left
        (fun (results, acc) (lab, arg) ->
          let acc = (lab, arg) :: acc in
          match lab with
          | Boundary -> (List.rev acc)::results, []
          | _ -> results, acc
        )
        ([], [])
        args
    in
    let args_s = List.rev args_s in
    let args_s =
      let to_no_insert xs = List.map (fun (_, ty) -> (NoInsert, ty)) xs in
      List.map
        (fun args ->
          if List.exists (fun (_, arg) -> is_ho arg) args then begin
            match args with
            | (_, ty)::xs -> (Insert, ty)::(to_no_insert xs)
            | _ -> assert false
          end else (to_no_insert args)
        )
        args_s in
    let args =
      List.flatten args_s
      |> List.map (fun (lab, ty) -> (lab, border_to_insert_ty ty)) in
    let ty = compose_fun_ty (args) TBool in
    (* print_endline "border_to_insert_ty (after)";
    print_endline @@ show_i_ptype ty; *)
    ty
  end
  
(* borderで分割。分割した各領域に対して高階の引数があるなら、その領域の最初のTFuncに追加 *)

let border_to_insert_expr phi =
  let rec go phi : (insert_flag ptype, insert_flag) thflz=
    match phi with
    | Bool b -> Bool b
    | Arith a -> Arith (go_arith a)
    | Pred (p, a) -> Pred (p, (List.map go_arith a))
    | Var v -> Var { v with ty = border_to_insert_ty v.ty }
    | Or (p1, p2) -> Or (go p1, go p2)
    | And (p1, p2) -> And (go p1, go p2)
    | Abs _ -> begin
      let rec get_abs acc phi = match phi with
        | Abs (l, x, p) -> (get_abs ((l, x)::acc) p)
        | _ -> List.rev acc, phi
      in
      let args, body = get_abs [] phi in
      (* print_endline @@ show_p_hflz phi; *)
      (* assert (List.rev args |> List.hd |> fst = Boundary); *)
      let body = go body in
      let ty = get_thflz_type phi in
      let ty = border_to_insert_ty ty in
      let rec mk_abs (ty : insert_flag ptype) args body = match ty, args with
        | TFunc (lab, arg_ty, ty), (_, arg)::args ->
          assert (arg_ty = border_to_insert_ty arg.Id.ty);
          Abs (lab, { arg with ty = arg_ty }, mk_abs ty args body)
        | TBool, [] -> body
        | _ -> assert false
      in
      mk_abs ty args body
    end
    | Forall (x, p) ->
      assert (x.ty == TInt);
      Forall ({ x with ty = TInt}, go p)
    | Exists (x, p) ->
      assert (x.ty == TInt);
      Exists ({ x with ty = TInt}, go p)
    | App (p1, p2) ->
      App (go p1, go p2)
  and go_arith a = match a with
    | Int i -> Int i
    | Var v -> Var {v with ty=TInt}
    | Op (e, p) -> Op (e, List.map go_arith p)
  in
  go phi

let border_to_insert_rules rules =
  List.map
    (fun (var, args, body, fix) ->
      let var = { var with Id.ty = border_to_insert_ty var.Id.ty } in
      let args = List.map (fun arg -> { arg with Id.ty = border_to_insert_ty arg.Id.ty }) args in
      let body = border_to_insert_expr body in
      let rec g args ty = match args, ty with
        | x::xs, TFunc (l, _, b) -> Abs (l, x, g xs b)
        | [], TBool -> body
        | _ -> assert false
      in
      let body = g args var.ty in
      { var; fix; body }
    )
    rules
  
(* TODO: debug *)
let infer_partial_applications (hes : 'a Hflz.hes) : i_thflz_rule list =
  let rules = Hflz.merge_entry_rule hes in
  let rules = to_thflzs rules in
  (* print_endline "to_thflz";
  print_endline @@ show_s_thes_rules rules; *)
  let rules = infer_thflz_type rules in
  (* print_endline "infer_thflz_type (1)";
  print_endline @@ show_s_thes_rules rules; *)
  print_endline @@ show_p_hflz_hes rules;
  let rules = border_to_insert_rules rules in
  print_endline @@ show_i_hflz_hes rules;
  rules

let rec to_insert_all_ty ty =
  let is_ho ty = match ty with
    | TFunc _ -> true
    | _ -> false
  in
  match ty with
  | Type.TyArrow ({ty=argty; _}, ty) -> begin
    let argty = to_insert_all_arg_ty argty in
    let ty = to_insert_all_ty ty in
    if is_ho argty then
      TFunc (Insert, argty, ty)
    else
      TFunc (NoInsert, argty, ty)
  end
  | Type.TyBool _ -> TBool
and to_insert_all_arg_ty argty =
  match argty with
  | Type.TyInt -> TInt
  | Type.TySigma ty -> to_insert_all_ty ty

let insert_all_expr phi =
  let rec go phi =
    match phi with
    | Hflz.Bool b -> Bool b
    | Var v -> Var { v with ty = to_insert_all_ty v.ty }
    | Or (p1, p2) -> Or (go p1, go p2)
    | And (p1, p2) -> And (go p1, go p2)
    | Abs (x, p1) -> begin
      let flag =
        match x.ty with
        | Type.TyInt -> NoInsert
        | TySigma _ -> Insert
      in
      Abs (flag, { x with ty = to_insert_all_arg_ty x.ty }, go p1)
    end
    | Forall (x, p1) ->
      Forall ({x with ty=TInt}, go p1)
    | Exists (x, p1) ->
      Exists ({x with ty=TInt}, go p1)
    | App (p1, p2) ->
      App (go p1, go p2)
    | Arith a ->
      Arith (go_arith a)
    | Pred (op, a) ->
      Pred (op, List.map go_arith a)
  and go_arith a =
    match a with
    | Int i -> Int i
    | Var v -> Var { v with ty = TInt }
    | Op (op, a) -> Op (op, List.map go_arith a)
  in
  go phi

let insert_all (hes : 'a Hflz.hes) : i_thflz_rule list =
  let rules = Hflz.merge_entry_rule hes in
  let rules =
    List.map
      (fun {Hflz.var; body; fix} ->
        let var = { var with ty = to_insert_all_ty var.ty } in
        let body = insert_all_expr body in
        { var; body; fix }
      )
      rules in
  rules
