open Hflmc2_util
open Id
open Type
open Hflz

let show_sort sort =
  match sort with
  | Ast.Logic.Sort.SDummy -> "SDummy"
  | Ast.Logic.T_bool.SBool  -> "SBool"
  | Ast.Logic.T_int.SInt   -> "SInt"
  | _ -> failwith "show_sort"
  
let conv_ty_sub ty =
  match ty with
  | Ast.Logic.T_bool.SBool -> TySigma (TyBool ())
  | Ast.Logic.T_int.SInt -> TyInt
  | _ -> failwith "conv_ty"

let conv_ty_pvar tys arg_names = 
  print_endline "show_typ";
  print_endline @@ String.concat ~sep:";" (List.map ~f:show_sort tys);
  let tys = List.map ~f:conv_ty_sub tys in
  let ty = 
    let rec go' (tys, arg_names) =
      match tys, arg_names with
      (* | [] -> failwith "tys 1" *)
      | [], [] -> TyBool ()
      | x::xs, n::ns -> TyArrow (Id.gen ~name:n x, go' (xs, ns))
      | _ -> failwith "go'" in
    TySigma (go' (tys, arg_names))
  in
  ty

let direct_find env k = List.find env ~f:(fun (k', v) -> k' = k) |> (fun a -> match a with None -> None | Some (a, b) -> Some b)

let add_env_pvar env (k, tys) arg_names =
  match direct_find env (`Pvar k) with
  | Some _ -> failwith "add_env_pvar"
  | None -> begin
    let (Ast.Ident.Pvar name) = k in
    print_endline "pvar key";
    print_endline name;
    let ty = conv_ty_pvar tys arg_names in
    let v = Id.gen ~name:name ty in
    let env = (`Pvar k, v)::env in
    (v, env)
  end
  
let add_env_tvar env (k, ty) =
  match direct_find env (`Tvar k) with
  | Some _ -> failwith "add_env (possible variable shadowing)"
  | None -> begin
    let (Ast.Ident.Tvar name) = k in
    print_endline "key";
    print_endline name;
    let ty = conv_ty_sub ty in
    let v = Id.gen ~name:name ty in
    let env = (`Tvar k, v)::env in
    (v, env)
  end
  
let rec go_arith env (arith : Ast.Logic.Term.t) : Arith.t =
  match arith with
  | Var (tvar, sort, _) -> begin
    match direct_find env (`Tvar tvar) with
    | None -> (let Tvar t = tvar in failwith @@ "arith var " ^ t)
    | Some v -> 
      Var ({ v with ty=`Int })
  end
  | FunApp (fun_sym, args, _) -> begin
    match fun_sym with
    | Ast.Logic.T_int.Int i -> begin
      match Bigint.to_int i with
      | Some i -> Arith.Int i
      | None -> failwith "to_int"
    end
    | Ast.Logic.T_int.Add -> Op (Add, List.map ~f:(go_arith env) args)
    | Ast.Logic.T_int.Sub -> Op (Sub, List.map ~f:(go_arith env) args)
    | Ast.Logic.T_int.Mult-> Op (Mult,List.map ~f:(go_arith env) args)
    | Ast.Logic.T_int.Div -> Op (Div, List.map ~f:(go_arith env) args)
    | Ast.Logic.T_int.Mod -> Op (Mod, List.map ~f:(go_arith env) args)
    | _ -> failwith "fun_app"
  end
  
let rec go env (f : Ast.Logic.Formula.t) : Type.simple_ty t =
  match f with
  | Atom (True _, _) -> Bool true
  | Atom (False _, _) -> Bool false
  | Atom (App (Psym psym, args, _), _) -> begin
    let args = List.map ~f:(go_arith env) args in
    match psym with
    | Ast.Logic.T_bool.Eq -> Pred(Eq, args)
    | Ast.Logic.T_bool.Neq -> Pred(Neq, args)
    | Ast.Logic.T_int.Leq -> Pred(Le, args)
    | Ast.Logic.T_int.Geq -> Pred(Ge, args)
    | Ast.Logic.T_int.Lt -> Pred(Lt, args)
    | Ast.Logic.T_int.Gt -> Pred(Gt, args)
    | _ -> failwith "psym"
  end
  | Atom (App (Var (p, sorts), args, _), _) -> begin
    let args = List.map ~f:(go_arith env) args |> List.map ~f:(fun f -> Arith f) in
    let rec go' acc = function
      | [x] -> App (acc, x)
      | x::xs -> go' (App (acc, x)) xs
      | [] -> acc in
    match direct_find env (`Pvar p) with
    | None -> failwith "atom app"
    | Some ({ ty=TySigma t; _} as v) -> 
      go' (Var ({ v with ty=t })) args
    | _ -> failwith "atom app 2"
  end
  | Atom (App (Fixpoint _, _, _), _) -> failwith "atom app fixpoint"
  | UnaryOp (Neg, _, _) -> failwith "neg"
  | BinaryOp (And, f1, f2, _) ->
    And (go env f1, go env f2)
  | BinaryOp (Or, f1, f2, _) ->
    Or (go env f1, go env f2)
  | BinaryOp (_, _, _, _) -> failwith "bin"
  | Bind (Forall, args, f, _) ->
    let rec go' env = function
      | (tvar, s)::xs -> 
        let (v, env) = add_env_tvar env (tvar, s) in
        Forall (v, go' env xs)
      | [] -> go env f in
    go' env args
  | Bind (Exists, args, f, _) ->
    let rec go' env = function
      | (tvar, s)::xs -> 
        let (v, env) = add_env_tvar env (tvar, s) in
        Exists (v, go' env xs)
      | [] -> go env f in
    go' env args
  | LetRec _ -> failwith "letrec"

let of_fix fix =
    match fix with
    | Ast.Logic.Predicate.Mu -> Fixpoint.Least
    | Ast.Logic.Predicate.Nu -> Fixpoint.Greatest
  
let of_func env (fix, pvar, ass, f) =
  let var = match direct_find env (`Pvar pvar) with
  | None -> failwith "of_func"
  | Some var -> var in
  let var = match var.ty with
    | TySigma ty -> { var with ty=ty }
    | TyInt -> failwith "var.ty" in
  let rec go' env ass =
    match ass with
    | [] -> go env f
    | (arg, sort)::xs -> begin
      let (v, env) = add_env_tvar env (arg, sort) in
      Abs (v, go' env xs)
    end in
  { fix=of_fix fix; var=var; body=go' env ass }

let do_env env (fix, pvar, ass, f) = 
  let sorts = List.map ~f:(fun (a, s) -> s) ass in
  let args = List.map ~f:(fun (Ast.Ident.Tvar a, s) -> a) ass in
  let (_, env) = add_env_pvar env (pvar, sorts) args in
  env
  
let of_hes (Hes.HesLogic.Hes (funcs, ep)) =
  let env = List.fold_left funcs ~init:[] ~f:(fun env r -> do_env env r) in
  let top = go env ep in
  let top_rule = { fix=Fixpoint.Greatest; var=Id.gen ~name:"Sentry" (TyBool ()); body=top} in
  top_rule::(List.map ~f:(of_func env) funcs)