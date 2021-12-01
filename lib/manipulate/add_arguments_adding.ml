open Hflmc2_syntax
module Env = Env_no_value

open Add_arguments_tuple

let log_src = Logs.Src.create "Add_arguments_adding"
module Log = (val Logs.src_log @@ log_src)

let log_string = Hflz_util.log_string Log.info

let generated_ids = Hashtbl.create 10

let extra_arg_name = "sssss"
let extra_param_name = "ttttt"

let id_gen ?name ty =
  let id = T.id_gen ?name ty in
  (match name with
  | Some s -> begin
    let id = Id.remove_ty id in
    match Hashtbl.find_opt generated_ids s with
    | Some ls ->
      let ls = (s, id)::ls in
      Hashtbl.replace generated_ids s ls
    | None ->
      Hashtbl.add generated_ids s [(s, id)]
  end
  | None -> ());
  id
  
module Simplify = struct
  open Hflmc2_syntax

  let rec gen_arith_ (**: Print.Prec.t -> 'avar Arith.gen_t*) =
    fun prec ppf a ->
      let show_op = function | (Arith.Op (op',[a1;a2])) -> begin
        let op_prec = Print.Prec.of_op op' in
        let prec_l = Print.Prec.(succ_if (not @@ op_is_leftassoc op') op_prec) in
        let prec_r = Print.Prec.(succ_if (not @@ op_is_rightassoc op') op_prec) in
        Print.show_paren (prec > op_prec) ppf "@[<1>%a@ %a@ %a@]"
          (gen_arith_ prec_l) a1
          Print.op op'
          (gen_arith_ prec_r) a2
      end | _ -> assert false
      in
      match a with
      | Int n ->
        if n >= 0 then
          Fmt.int ppf n
        else
          (Fmt.string ppf "("; Fmt.int ppf n; Fmt.string ppf ")";)
      | Var x -> Print.fprintf ppf "%s" (Id.to_string x)
      | Op (Sub,[Int 0; a']) ->
          Print.show_paren (prec > Print.Prec.neg) ppf "-%a"
            (gen_arith_ Print.Prec.(succ neg)) a'
      | Op _ -> show_op a
      
  type 'a arith2 =
    | Int of int
    | AddOp of 'a arith2 list
    | MulOp of 'a arith2 list
    | Arith of 'a Id.t Arith.gen_t

  let rec show_arith2 a = match a with
    | Int i -> string_of_int i
    | AddOp ps -> "(" ^ (List.map show_arith2 ps |> String.concat "+") ^ ")"
    | MulOp ps -> "(" ^ (List.map show_arith2 ps |> String.concat "*") ^ ")"
    | Arith a -> Hflmc2_util.fmt_string (gen_arith_ Print.Prec.zero) a
    
  let simplify a =
    let rec go_list a = match a with
      | Arith.Int i -> Int i
      | Op (Add, ps)  -> begin
        let rec g p = match p with
          | Arith.Op (Add, ps) -> List.map g ps |> List.flatten
          | _ -> [go_list p]
        in
        AddOp (List.map g ps |> List.flatten)
      end
      | Op (Mult, ps) -> begin
        let rec g p = match p with
          | Arith.Op (Mult, ps) -> List.map g ps |> List.flatten
          | _ -> [go_list p]
        in
        MulOp (List.map g ps |> List.flatten)
      end
      | _ -> Arith a
    in
    let rec from_list a = match a with
      | Int i -> Arith.Int i
      | Arith a -> a
      | AddOp ls ->
        let rec g = function
          | [] -> assert false
          | [x] -> from_list x
          | [x; y] -> Op (Add, [from_list x; from_list y])
          | x::xs -> Op (Add, [(from_list x); g xs])
        in
        g ls
      | MulOp ls ->
        let rec g = function
          | [] -> assert false
          | [x] -> from_list x
          | [x; y] -> Op (Mult, [from_list x; from_list y])
          | x::xs -> Op (Mult, [(from_list x); g xs])
        in
        g ls
    in
    let a = go_list a in
    (* print_endline "go_list";
    print_endline @@ show_arith2 a; *)
    let rec distribute a =
      (* print_endline "distribute (1)";
      print_endline @@ show_arith2 a; *)
      let flatten_mult' a = MulOp (flatten_mult a) in
      let flatten_add' a = AddOp (flatten_add a) in
      let distr v ps =
        (* print_endline "distr (1)"; *)
        AddOp (List.map (fun p -> flatten_mult' (MulOp [v; p]) |> calc) ps)
      in
      match a with
      | MulOp ([Int i; AddOp ps]) -> distr (Int i) ps |> flatten_add' |> calc
      | MulOp ([AddOp ps; Int i]) -> distr (Int i) ps |> flatten_add' |> calc
      | MulOp ([AddOp ps; Arith (Var v)]) -> distr (Arith (Var v)) ps |> flatten_add' |> calc
      | MulOp ([Arith (Var v); AddOp ps]) -> distr (Arith (Var v)) ps |> flatten_add' |> calc
      | MulOp ps -> MulOp (List.map distribute ps) |> flatten_mult' |> calc
      | AddOp ps -> AddOp (List.map distribute ps) |> flatten_add' |> calc
      | Int i -> Int i
      | Arith a -> Arith a
    and flatten_mult a = match a with
      | MulOp (vs) -> List.map flatten_mult vs |> List.flatten
      | _ -> [a]
    and flatten_add a = match a with
      | AddOp (vs) -> List.map flatten_add vs |> List.flatten
      | _ -> [a]
    and calc ls =
      (* print_endline "calc (1)"; *)
      (* ls *)
      match ls with
      | MulOp xs -> begin
        (* print_endline "mulop";
        List.iter (fun x -> print_endline @@ show_arith2 x) xs; *)
        let is, xs = List.partition (fun x -> match x with Int _ -> true | _ -> false) xs in
        if List.length is > 0 then begin
          let is =
            List.map
              (fun x -> match x with Int i -> i | _ -> assert false)
              is
            |> List.fold_left (fun a b -> a * b) 1 in
          (* print_endline "mulop 2";
          List.iter (fun x -> print_endline @@ show_arith2 x) ((Int is)::xs); *)
          if is = 1 then (if List.length xs = 0 then Int 1 else MulOp xs)
          else if is = 0 then Int 0
          else MulOp ((Int is)::xs)
        end else begin
          (* print_endline "mulop 3";
          List.iter (fun x -> print_endline @@ show_arith2 x) (xs); *)
          MulOp xs
        end
      end
      | AddOp xs -> begin
        (* print_endline "addop";
        List.iter (fun x -> print_endline @@ show_arith2 x) xs; *)
        let is, xs = List.partition (fun x -> match x with Int _ -> true | _ -> false) xs in
        if List.length is > 0 then begin
          let is =
            List.map
              (fun x -> match x with Int i -> i | _ -> assert false)
              is
            |> List.fold_left (fun a b -> a + b) 0 in
          (* print_endline "addop 2";
          List.iter (fun x -> print_endline @@ show_arith2 x) ((Int is)::xs); *)
          if is = 0 then (if List.length xs = 0 then Int 0 else MulOp xs)
          else MulOp ((Int is)::xs)
        end else begin
          (* print_endline "addop 3";
          List.iter (fun x -> print_endline @@ show_arith2 x) (xs); *)
          MulOp xs
        end
      end
      | _ -> ls
    in
    let rec go a =
      let a' = distribute a in
      if a' <> a then go a' else a
    in
    let a = go a in
    (* print_endline "distribute";
    print_endline @@ show_arith2 a; *)
    from_list a
  
  let standarize a =
    match a with
    | Arith.Var x -> Arith.Op (Add, [Op (Mult, [Int 1; Var x]); Int 0])
    | Op (Add, [Var x; Int i]) ->
      Op (Add, [Op (Mult, [Int 1; Var x]); Int i])
    | Op (Mult, [Int i; Var x]) -> 
      Op (Add, [Op (Mult, [Int i; Var x]); Int 0])
    | _ -> a
(*   
  let a () =
    let v = Id.gen `Int in
    let phi = simplify (Op (Add, [Op (Mult, [Int 1; Op (Add, [Op (Mult, [Int 1; Var v]); Int 0])]); Int 0])) in
    let phi = simplify (Op (Add, [Op (Add, [Int 1; Op (Add, [Op (Mult, [Int 1; Var v]); Int 0])]); Int 0])) in
    () *)
end

type ptype' = TInt' | TBool' | TFunc' of ptype' * ptype'
[@@deriving eq,ord]

let rec pp_ptype' prec ppf ty =
  match ty with
  | TBool' ->
    Fmt.pf ppf "bool"
  | TInt' ->
    Fmt.pf ppf "int"
  | TFunc' (ty1, ty2) ->
    Print.show_paren (prec > Print.Prec.arrow) ppf "@[<1>%a ->@ %a@]"
      (pp_ptype' Print.Prec.(succ arrow)) ty1
      (pp_ptype' Print.Prec.arrow) ty2

let show_ptype' = Hflmc2_util.fmt_string (pp_ptype' Print.Prec.zero) 

let get_thflz_type_without_check' phi =
  let rec go phi = match phi with
    | T.Bool _ -> TBool'
    | Var v -> v.ty
    | Or _ -> TBool'
    | And _ -> TBool'
    | Abs (_, _, lty) -> lty
    | Forall (_, body) -> go body
    | Exists (_, body) -> go body
    | App (p1, _) -> begin
      let ty1 = go p1 in
      match ty1 with
      | TFunc' (_, t2) -> t2
      | _ -> assert false
    end
    | Pred (_, _) -> TBool'
    | Arith _ -> TInt'
  in
  go phi

let show_pt_thflz (body : ptype' T.thflz) = 
  Hflmc2_util.fmt_string
    (T.Print_temp.hflz_ get_thflz_type_without_check' (fun _ -> "") pp_ptype') body

let show_pt_thflz2 phi = Hflmc2_util.fmt_string (Print_temp.hflz pp_ptype2) phi

(* let print_pt_thflz body = print_endline @@ show_pt_thflz body *)

let should_add ty f =
  match ty with
  | TFunc _ -> begin
    match f with
    | T.TUse -> true
    | TNotUse -> false
    | EFVar _ -> assert false
  end
  | _ -> false

let rec convert_ty' ty : ptype' = match ty with
  | TFunc (argtys, bodyty) -> begin
    let rec to_tfunc2 argtys bodyty = match argtys with
      | ty::tys -> TFunc' (ty, to_tfunc2 tys bodyty)
      | [] -> bodyty in
    let argtys' = List.map (fun (argty, _) -> convert_ty' argty) argtys in
    if List.exists (fun (argty, tag) -> should_add argty tag) argtys then
      TFunc' (
        TInt',
        to_tfunc2 argtys' (convert_ty' bodyty)
      )
    else
      to_tfunc2 argtys' (convert_ty' bodyty)
  end
  | TBool -> TBool'
  | TInt -> TInt'
  | TVar _ -> assert false

let fold_formula f xs =
  match xs with
  | a::xs -> begin
    let rec go acc = function
      | x::xs -> go (f acc x) xs
      | [] -> acc
    in
    go a xs
  end
  | [] -> failwith "fold_formula: should have more than 0 elements"
  
let make_bounds simplifier xs c1 c2 r =
  let bounds =
    List.map
      (fun x ->
        (* r < (c1 * x) + c2, r < (-c1 * x) + c2 *)
        [ T.Pred (Lt, [Var r; simplifier (Arith.Op (Add, [(Op (Mult, [Int c1; x])); Int c2])) |> Simplify.standarize]);
          Pred (Lt, [Var r; simplifier (Op (Add, [(Op (Mult, [Int (-c1); x])); Int c2])) |> Simplify.standarize])]
      )
      xs
    |> List.concat in
  let bounds = Hflmc2_util.remove_duplicates (=) bounds in
  (bounds @ [T.Pred (Lt, [Var r; Int c2])]) |> fold_formula (fun acc f -> T.Or (acc, f))

(* check that a body of Abses has bool type *)
let check_t1 rules =
  let rec go phi = match phi with
    | Bool _ -> ()
    | Var _ -> ()
    | Or (p1, p2) ->
      go p1;
      go p2
    | And (p1, p2) ->
      go p1; go p2
    | Abs (_, phi, ty) -> begin
      match phi with
      | Abs _ -> ()
      | _ -> begin
        match ty with
        | TBool -> go phi
        | _ -> assert false
      end
    end
    | Forall (_, p) ->
      go p
    | Exists (_, p) ->
      go p
    | App (p1, ps) ->
      go p1;
      List.iter go ps
    | Arith _ -> ()
    | Pred _ -> ()
  in
  List.map (fun {body; _} -> go body) rules

let rec to_int_type x = match x with
  | Arith.Int i -> Arith.Int i
  | Var v -> Var {v with Id.ty=`Int}
  | Op (op, xs) -> Op (op, List.map to_int_type xs)

let get_free_variables_in_arith a =
  let rec go a = match a with
    | Arith.Op (_, xs) -> List.map go xs |> List.flatten
    | Int _ -> []
    | Var x -> [x]
  in
  go a

let make_bounds' simplifier (id_type_map : (unit Id.t, Hflz_util.variable_type, IdMap.Key.comparator_witness) Base.Map.t
ref
) (add_args : (ptype' Id.t Arith.gen_t list * int * int * ptype' Id.t) list) (body : ptype' T.thflz) : ptype' T.thflz =
  let rec go = function
    | (xs, c1, c2, r)::add_args ->
      log_string @@ "make_bounds': " ^ Id.to_string r;
      let gen_ids =
        Option.value (Hashtbl.find_opt generated_ids extra_arg_name) ~default:[] in
      let xs =
        List.filter
          (fun x ->
            let fvs = get_free_variables_in_arith x in
            not @@
            List.exists
              (fun fv ->
                List.exists
                  (fun (_, x') -> Id.eq fv x')
                  gen_ids
              )
              fvs
          )
          xs in
      (* TDOO: *)
      id_type_map := IdMap.add !id_type_map ({r with Id.ty=Type.TyInt}) (Hflz_util.VTVarMax (List.map to_int_type xs |> Hflmc2_util.remove_duplicates (=)));
      let bounds = make_bounds simplifier xs c1 c2 r in
      T.Forall (r, Or (bounds, go add_args))
    | [] ->
      body
  in
  go add_args

let make_bounds_if_body_is_bool simplifier id_type_map psi ty add_args =
  match ty with
  | TBool' ->
    make_bounds' simplifier id_type_map add_args psi
  | TFunc' _ -> begin
    if List.length add_args > 0 then assert false;
    psi
  end
  | TInt' -> assert false

let show_thflz' rules =
  List.map (fun (var, body, fix) ->
    Id.to_string var ^ " =" ^ show_fixpoint fix ^ 
    show_pt_thflz body
  ) rules
  |> String.concat ".\n"


let get_occuring_arith_terms phi added_vars = 
    (* print_endline "get_occuring_arith_terms phi:";
      print_endline @@ show_pt_thflz phi; *)
  (* remove expressions that contain locally bound variables *)
  let remove ls x =
    List.filter (fun (_, vars) -> not @@ List.exists ((=) (Id.remove_ty x)) vars) ls
  in
  let rec go_hflz phi = match phi with
    | T.Bool _ -> []
    | Var _ -> [] (* use only arithmetic variable *)
    | Or (p1, p2) -> (go_hflz p1) @ (go_hflz p2)
    | And (p1, p2) -> (go_hflz p1) @ (go_hflz p2)
    | Abs (x, p1, _) -> remove (go_hflz p1) x
    | Forall (x, p1) -> remove (go_hflz p1) x
    | Exists (x, p1) -> remove (go_hflz p1) x
    | App (p1, p2) -> (go_hflz p1) @ (go_hflz p2)
    | Arith (Int 0) -> [] (* ignore *)
    | Arith a -> [(a, get_occurring_arith_vars a)]
    | Pred (Lt, [Var s; _]) when List.exists (fun v -> Id.eq v s) added_vars ->
      (* for added variables for ho-variables, add nothing *)
      []
    | Pred (_, xs) ->
      (* print_endline "get_occuring_arith_terms:";
      print_endline @@ show_pt_thflz phi; *)
      xs
      |> List.filter (fun a -> a <> Arith.Int 0)
      |> List.map (fun a -> (a, get_occurring_arith_vars a))
  and get_occurring_arith_vars phi = match phi with
    | Int _ -> []
    | Var v -> [Id.remove_ty v]
    | Op (_, xs) -> List.map get_occurring_arith_vars xs |> List.concat
  in
  go_hflz phi |> List.map fst

type will_create_bound = CreateBound | NotCreateBound

let get_global_env {var_in_out; body; _} outer_mu_funcs (global_env : ptype2 T.in_out Id.t list) =
  let lookup v env =
    List.find (fun (id, _) -> Id.eq id v) env |> snd in
  let env_has v env =
    match List.find_opt (fun v' -> Id.eq v' v) env with
    | Some _ -> true
    | None -> false
  in
  let current_outer_pvars = lookup var_in_out outer_mu_funcs in
  let global_preds =
    get_free_variables body
    |> List.filter (fun v -> Id.is_pred_name v.Id.name) in
  global_preds
  |> List.map (fun pvar ->
    let arg_pvars = lookup pvar outer_mu_funcs in
    let new_pvars =
      List.filter (fun pvar -> not @@ env_has pvar current_outer_pvars) arg_pvars in
    (* var_in_outと、追加するpredicateが一致しないことがある。しかし、どちらにせよその引数として渡されている値は最小不動点の中で使う可能性があるので、単にタグをTにすればよい *)
    let pvar_e = List.find (fun v -> Id.eq v pvar) global_env in
    if new_pvars = [] then
      {pvar with ty=pvar_e.ty.T.inner_ty}, NotCreateBound, pvar_e.ty.T.inner_ty
    else
      {pvar with ty=pvar_e.ty.outer_ty}, CreateBound, pvar_e.ty.T.inner_ty
  )

let add_params c1 c2 outer_mu_funcs (rules : ptype2 thes_rule_in_out list) =
  Hashtbl.reset generated_ids;
  let simplifier = fun x -> x in
  (* let simplifier = Simplify.simplify in *)
  let id_type_map = ref IdMap.empty in  (* 整数変数 -> その「タイプ」 *)
  let id_ho_map = ref [] in  (* 高階の変数 -> その情報を持つ整数変数 *)
  let rec go_app body ps = match ps with
    | p::ps ->
      T.App (go_app body ps, p)
    | [] -> body
  in
  let rec go_abs body bodyty xs = match xs with
    | x::xs -> begin
      let b, tybody = go_abs body bodyty xs in
      let ty = TFunc' (x.Id.ty, tybody) in
      T.Abs (x, b, ty), ty
    end
    | [] -> body, bodyty
  in
  let rec go
      (global_env : (ptype2 Id.t * will_create_bound * ptype2) list)
      (rho : (ptype' Id.t * ptype' Id.t) list)
      (phi : ptype2 thflz2) : ptype' T.thflz * ptype' * ((ptype' Id.t Arith.gen_t list * int * int * ptype' Id.t) list) = match phi with
    | Abs (xs, psi, ty) -> begin
      let argty_tags, _ =
        match ty with
        | TFunc (argty_tags, tybody) -> argty_tags, tybody
        | _ -> assert false in
      let will_add = List.exists (fun (ty, t) -> should_add ty t) argty_tags in
      let xs = List.map (fun x -> { x with Id.ty = convert_ty' x.Id.ty }) xs in
      if will_add then begin
        (* add param *)
        let k = id_gen ~name:extra_param_name TInt' in
        let psi, ty, add_args =
          let rho' =
            List.filter_map
              (fun (x, (ty, t)) ->
                if should_add ty t then
                  Some (x, k)
                else None
              )
              (List.combine xs argty_tags)
            in
          go global_env (rho' @ rho) psi in
        let psi = make_bounds_if_body_is_bool simplifier id_type_map psi ty add_args in
        let psi, ty = go_abs psi ty xs in
        let ty2 = TFunc' (TInt', ty) in
        id_type_map := IdMap.add !id_type_map k (Hflz_util.VTHigherInfo (Some (Id.remove_ty k, List.map Id.remove_ty xs)));
        T.Abs (k, psi, ty2), ty2, []
      end else begin
        let psi, ty, add_args = go global_env rho psi in
        let psi = make_bounds_if_body_is_bool simplifier id_type_map psi ty add_args in
        let psi, ty = go_abs psi ty xs in
        psi, ty, []
      end
    end
    | App (p1, ps) -> begin
      let ty1_ = get_thflz2_type_without_check p1 in
      let argty_tags, _ =
        match ty1_ with
        | TFunc (argty_tags, tybody) -> argty_tags, tybody
        | _ -> assert false in
      let p1, ty1, add_args1 = go global_env rho p1 in
      (* print_endline "phi 2";
      print_endline @@ show_pt_thflz2 phi;
      print_endline "ty1_";
      print_endline @@ show_ptype2 ty1_;
      print_endline "ty1";
      print_endline @@ show_ptype' ty1; *)
      let ps' = List.map (go global_env rho) ps in
      let ps_ = List.map (fun (p, _, _) -> p) ps' in
      let ty2s = List.map (fun (_, ty, _) -> ty) ps' in
      let add_args2 = List.map (fun (_, _, a) -> a) ps' |> List.flatten in
      let will_add = List.exists (fun (ty, t) -> should_add ty t) argty_tags in
      (* print_endline "phi 3";
      print_endline @@ show_pt_thflz2 phi;
      print_endline "argty (entry)";
      print_endline @@ show_ptype' ty1;
      print_endline "ty2 (entry)";
      List.iter (fun ty2 -> print_endline @@ show_ptype' ty2) ty2s; *)
      if will_add then begin
        (* add arg *)
        let xs : ptype' Id.t Arith.gen_t list =
          let fvs =
            List.filter_map
              (fun (p, (ty, tag)) ->
                if should_add ty tag then
                  Some (T.get_free_variables p) (* TODO: aa *)
                else
                  None
              )
              (List.combine ps_ argty_tags)
            |> List.flatten
          in
          (List.filter_map
            (fun fv ->
              match fv.Id.ty with
              | TInt' -> Some (Arith.Var fv)
              | TFunc' _ -> begin
                match List.find_opt (fun (id, _) -> Id.eq id fv) rho with
                | Some (_, i) -> Some (Var i)
                | None -> None
              end
              | TBool' -> None
            )
            fvs)
          in
        (* print_endline "phi 1";
        print_endline @@ show_pt_thflz2 phi;
        print_endline "ty1_";
        print_endline @@ show_ptype2 ty1_; *)
        let xs =
          xs @
          (List.filter_map
            (fun (p, (ty, tag)) ->
              if should_add ty tag then begin
                (* print_endline "get11";
                print_endline @@ show_ptype2 ty;
                print_endline @@ T.show_use_flag tag;
                print_endline @@ show_pt_thflz p; *)
                (* TODO: mutable referenceで良くない *)
                let added_vars = IdMap.keys !id_type_map in
                Some (get_occuring_arith_terms p added_vars)
              end else
                None
            )
            (List.combine ps_ argty_tags)
          |> List.flatten)
        in
        let r = id_gen ~name:extra_arg_name TInt' in
        let bodyty =
          let rec go_app ty1 ty2s = match ty1, ty2s with
            | TFunc' (argty, bodyty), ty2::ty2s ->
              (* print_endline "argty (add)";
              print_endline @@ show_ptype' argty;
              print_endline "ty2 (add)";
              print_endline @@ show_ptype' ty2; *)
              assert (argty = ty2);
              go_app bodyty ty2s
            | _, [] -> ty1
            | _ -> assert false
          in
          go_app ty1 (TInt'::ty2s)
        in
        go_app (App (p1, Arith (Var r))) (List.rev ps_),
        bodyty,
        ((xs, c1, c2, r) :: add_args1 @ add_args2)
      end else begin
        let bodyty =
          let rec go_app ty1 ty2s = match ty1, ty2s with
            | TFunc' (argty, bodyty), ty2::ty2s ->
              (* print_endline "argty";
              print_endline @@ show_ptype' argty;
              print_endline "ty2";
              print_endline @@ show_ptype' ty2; *)
              assert (argty = ty2);
              go_app bodyty ty2s
            | _, [] -> ty1
            | _ -> assert false
          in
          go_app ty1 ty2s
        in
        go_app p1 (List.rev ps_), bodyty, add_args1 @ add_args2
      end
    end
    | Var v -> begin
      match List.find_opt (fun (id, _, _) -> Id.eq id v) global_env with
      | Some (_, CreateBound, vt') ->
        (* boundを作るとき *)
        (* print_endline @@ "Var(before): " ^ Id.to_string v ^ ": " ^ show_ptype2 v.ty; *)
        (* eta-展開を行う *)
        (* 外側（Tが多い方）で引数を受け取る *)
        let rec go ty ty' = match ty, ty' with
          | TFunc (argtys, bodyty), TFunc (argtys', bodyty') -> begin
            let xs = List.map (fun (argty, _) -> id_gen (convert_ty' argty)) argtys in
            let fst =
              if List.exists (fun (argty, tag) -> assert (tag=T.TUse); should_add argty tag) argtys then begin
                let k = id_gen TInt' in
                List.iter
                  (fun x ->
                    id_ho_map := (Id.remove_ty x, {k with ty=`Int})::!id_ho_map;
                  )
                  xs;
                Some k
              end else None in
            let snd = List.exists (fun (argty, tag) -> should_add argty tag) argtys' in
            (fst, snd, xs) :: (go bodyty bodyty')
          end
          | TBool, TBool -> []
          | TInt, TInt | TVar _, TVar _ -> assert false
          | _ -> assert false in
        (* go outer_ty inner_ty *)
        let params = go v.ty vt' in
        let rec make_abs body (params : (ptype' Id.t option * bool * ptype' Id.t list) list) = match params with
          | (fst, _, xs)::xss -> begin
            let b, ty = make_abs body xss in
            let b, ty = go_abs b ty xs in
            match fst with
            | Some x' ->
              let ty2 = TFunc' (x'.Id.ty, ty) in
              T.Abs (x', b, ty2), ty2
            | None -> b, ty
          end
          | [] ->
            let ty = get_thflz_type_without_check' body in
            (* print_pt_thflz body;
            print_endline @@ "ty: " ^ show_ptype' ty; *)
            assert (ty = TBool');
            body, TBool'
        in
        let rec make_app body (params : (ptype' Id.t option * bool * ptype' Id.t list) list) = match params with
          | (fst, snd, xs) :: xss -> begin
            let xs =
              List.map
                (fun x ->
                  match x.Id.ty with
                  | TInt' -> T.Arith (Var {x with ty=TInt'})
                  | _ -> Var x
                )
                xs in
            if snd then begin
              let x' =
                match fst with
                | Some x' -> x'
                | None -> assert false
              in
              go_app (T.App (make_app body xss, Arith (Var x'))) (List.rev xs)
            end else
              go_app (make_app body xss) (List.rev xs)
          end
          | [] -> body in
        let v' = { v with ty = convert_ty' vt'} in
        (* print_endline "v'";
        print_endline @@ show_ptype' v'.ty; *)
        let b = make_app (Var v') (List.rev params) in
        let psi, ty'' = make_abs b params in
        (* print_endline @@ "Var(after): " ^ show_pt_thflz psi ^ ": " ^ show_ptype2 v.ty; *)
        assert (ty'' = convert_ty' v.ty);
        psi, ty'', []
      | Some (_, NotCreateBound, _) | None ->
        (* print_endline @@ Id.to_string v;
        print_endline @@ "Var(after): " ^ show_ptype2 v.ty; *)
        let ty = convert_ty' v.ty in
        (* print_endline @@ "Var(before): " ^ show_ptype' ty; *)
        Var {v with ty = ty}, ty, []
    end
    | Or (p1, p2) ->
      let p1, ty1, c1 = go global_env rho p1 in
      let p1 = make_bounds' simplifier id_type_map c1 p1 in
      let p2, ty2, c2 = go global_env rho p2 in
      let p2 = make_bounds' simplifier id_type_map c2 p2 in
      assert (ty1 = TBool' && ty2 = TBool');
      Or (p1, p2), TBool', []
    | And (p1, p2) ->
      let p1, ty1, c1 = go global_env rho p1 in
      let p1 = make_bounds' simplifier id_type_map c1 p1 in
      let p2, ty2, c2 = go global_env rho p2 in
      let p2 = make_bounds' simplifier id_type_map c2 p2 in
      assert (ty1 = TBool' && ty2 = TBool');
      And (p1, p2), TBool', []
    | Forall (x, p) ->
      let p, ty1, c1 = go global_env rho p in
      assert (ty1 = TBool');
      let p = make_bounds' simplifier id_type_map c1 p in
      Forall ({x with ty=convert_ty' x.ty}, p), TBool', []
    | Exists (x, p) ->
      let p, ty1, c1 = go global_env rho p in
      assert (ty1 = TBool');
      let p = make_bounds' simplifier id_type_map c1 p in
      Exists ({x with ty=convert_ty' x.ty}, p), TBool', []
    | Arith a -> Arith (go_arith a), TInt', []
    | Pred (op, ps) -> Pred (op, List.map go_arith ps), TBool', []
    | Bool b -> Bool b, TBool', []
  and go_arith a = match a with
    | Int i -> Int i
    | Var x -> Var {x with ty=TInt'}
    | Op (o, ps) -> Op (o, List.map go_arith ps)
  in
  let global_env = List.map (fun {var_in_out; _} -> var_in_out) rules in
  let rules =
    List.map
      (fun ({var_in_out; body; fix} as rule) ->
        let global_env =
          get_global_env rule outer_mu_funcs global_env in
        (* print_endline "start";
        print_endline @@ Id.to_string var_in_out;
        List.iter
          (fun (e, _, _) ->
            print_endline @@ Id.to_string e;
          )
          global_env;
        print_endline "end"; *)
        let body, ty, c = go global_env [] body in
        let body = make_bounds' simplifier id_type_map c body in
        assert ((convert_ty' var_in_out.ty.inner_ty) = ty);
        let var_in_out = { var_in_out with ty = convert_ty' var_in_out.ty.inner_ty} in
        (var_in_out, body, fix)
      )
      rules in
  (* print_endline "add_arguments_adding: add_params";
  print_endline @@ show_thflz' rules; *)
  rules, !id_type_map, !id_ho_map

let rec convert_ty ty = match ty with
  | TFunc' (argty, bodyty) ->
    let x = id_gen (convert_argty argty) in
    Type.TyArrow (x, convert_ty bodyty)
  | TBool' -> TyBool ()
  | TInt' -> failwith "cannot convert TInt'"
and convert_argty ty = match ty with
  | TInt' -> Type.TyInt
  | TFunc' _ | TBool' ->
    TySigma (convert_ty ty)
  
let to_hes (rules : (ptype' Id.t * ptype' T.thflz * T.fixpoint) list) =
  let rec go phi : unit Type.ty Hflz.t = match phi with
    | T.Var v ->
      (* print_endline @@ "to_hes VAR: " ^ v.name ^ "_" ^ string_of_int v.id; *)
      Var {v with ty = convert_ty v.ty}
    | Bool b -> Bool b
    | Or (p1, p2) -> Or (go p1, go p2)
    | And (p1, p2) -> And (go p1, go p2)
    | Abs (x, p, _) ->
      (* let rec go_abs xs = match xs with
        | x::xs ->  
          Hflz.Abs ({x with ty = convert_argty x.Id.ty}, go_abs xs)
        | [] -> go p
      in
      go_abs xs *)
      Abs ({x with ty = convert_argty x.Id.ty}, go p)
    | Forall (x, p) ->
      Forall ({x with ty = convert_argty x.ty}, go p)
    | Exists (x, p) ->
      Exists ({x with ty = convert_argty x.ty}, go p)
    | App (p1, p2) ->
      (* let rec go_app ps = match ps with
        | x::xs -> Hflz.App (go_app xs, go x)
        | [] -> go p1
      in
      go_app (List.rev ps) *)
      App (go p1, go p2)
    | Arith a ->
      Arith (go_arith a)
    | Pred (p, ps) ->
      Pred (p, List.map go_arith ps)
  and go_arith a = match a with
    | Int i -> Int i
    | Var x ->  
      assert (x.ty = TInt');
      Var {x with ty=`Int}
    | Op (p, ps) ->
      Op (p, List.map go_arith ps)
  in
  List.map
    (fun (var, body, fix) ->
      let var = {var with Id.ty=convert_ty var.Id.ty} in
      let body = go body in
      let fix =
        match fix with
        | T.Greatest -> Fixpoint.Greatest
        | Least -> Fixpoint.Least
      in
      {Hflz.var; body; fix}
    )
    rules


(* let () = Simplify.a () *)
