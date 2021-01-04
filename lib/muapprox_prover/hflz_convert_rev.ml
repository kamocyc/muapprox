open Hflmc2_util
module Id = Hflmc2_syntax.Id
module Type = Hflmc2_syntax.Type
module Arith = Hflmc2_syntax.Arith
module Hflz = Hflmc2_syntax.Hflz
module Fixpoint = Hflmc2_syntax.Fixpoint
open Id
open Type
module L = Ast.Logic

let dm = L.Dummy

let rec go_arith env (arg : Arith.t) : L.Term.t =
  match arg with
  | Arith.Var ( {name; ty = `Int; id} ) -> begin
    L.Term.Var (Tvar (name ^ string_of_int id), L.T_int.SInt, dm)
  end
  | Arith.Op (op, args) -> begin
    let op' = 
      match op with
      | Add -> L.T_int.Add
      | Sub -> L.T_int.Sub
      | Mult-> L.T_int.Mult
      | Div -> L.T_int.Div
      | Mod -> L.T_int.Mod
    in
    let args = List.map ~f:(go_arith env) args in
    FunApp (op', args, dm)
  end
  | Arith.Int i -> begin
    FunApp (L.T_int.Int (Bigint.of_int i), [], dm)
  end

let go_args_arith env (arg : simple_ty Hflz.t) =
  match arg with
  | Hflz.Arith a -> go_arith env a
  | _ -> failwith "go_args_arith"

let rec go_ty (ty : unit ty) : L.Sort.t list = 
  match ty with
  | TyBool () -> [L.T_bool.SBool]
  | TyArrow ({ty=TyInt; _}, rem) -> L.T_int.SInt :: (go_ty rem)
  | _ -> failwith "go_ty"
  
  
let log_src = Logs.Src.create "Main"
module Log = (val Logs.src_log @@ log_src)

let mk_var_app env (pname, pty, _, args) : L.Formula.t =
  let args = List.map ~f:(go_args_arith env) args in
  Atom (App (Var (Pvar (pname), go_ty pty), args, dm), dm)
  
let rec go env (f : Type.simple_ty Hflz.t) : L.Formula.t =
  match f with
  | Bool true  -> Atom (True dm, dm)
  | Bool false -> Atom (False dm, dm)
  | Pred (op, args) -> begin
    let args = List.map ~f:(go_arith env) args in
    let op' =
      match op with
      | Eq -> L.T_bool.Eq
      | Neq-> L.T_bool.Neq
      | Le -> L.T_int.Leq
      | Ge -> L.T_int.Geq
      | Lt -> L.T_int.Lt
      | Gt -> L.T_int.Gt in
    L.Formula.Atom (App (Psym op', args, dm), dm)
  end
  | Or (f1, f2)  -> BinaryOp (Or, go env f1, go env f2, dm)
  | And (f1, f2) -> BinaryOp (And, go env f1, go env f2, dm)
  | App _ as f -> begin
    let rec go' acc body =
      match body with
      | Hflz.App (Var ({name; ty; id}), arg) -> (name, ty, id, arg::acc)
      | Hflz.App (body, arg) -> go' (arg::acc) body
      | _ -> failwith "App go'" in
    let (pname, pty, pid, args) = go' [] f in
    mk_var_app env (pname, pty, pid, args)
  end
  | Forall ({ty=TyInt; id; _} as x, f) -> begin
    Bind (Forall, [(Tvar (x.name ^ string_of_int id), L.T_int.SInt)], go (x::env) f, dm)
  end
  | Exists ({ty=TyInt; id; _} as x, f) -> begin
    Bind (Exists, [(Tvar (x.name ^ string_of_int id), L.T_int.SInt)], go (x::env) f, dm)
  end
  | Var v ->
    mk_var_app env (v.name, v.ty, v.id, [])
  | _ ->
    Log.app begin fun m -> m ~header:"illegal" "%a" Manipulate.Print_syntax.(hflz simple_ty_) f end;
    failwith "go: illegal"

let of_fix fix =
  match fix with
  | Fixpoint.Least -> L.Predicate.Mu
  | Fixpoint.Greatest -> L.Predicate.Nu

let of_func env {Hflz.fix; body; var} =
  let rec go' acc body =
    match body with
    | Hflz.Abs ({ty=TyInt; name; id}, b) -> begin
      go' (acc@[Ast.Ident.Tvar (name ^ string_of_int id), L.T_int.SInt]) b
    end
    | _ -> acc, body in
  let args, body = go' [] body in
  ( of_fix fix, Ast.Ident.Pvar (var.name), args, go [] body)


let of_hes hes =
  Log.app begin fun m -> m ~header:"of_hes" "%a" Manipulate.Print_syntax.(hflz_hes simple_ty_) hes end;
  match hes with
  | [] -> failwith "of_hes"
  | frule::rem -> begin
    (* let rec_preds = Hflz_util.get_recurring_predicates hes in
    if List.exists ~f:(fun id -> id = frule.Hflz.var ) rec_preds then failwith "hflz_hes': First rule is recursive"; *)
    if frule.Hflz.var.ty <> TyBool () then failwith "hflz_hes': First rule has arguments";
    let ep = go [] frule.Hflz.body in
    let funcs = List.map ~f:(of_func []) rem in
    Hes.HesLogic.Hes (funcs, ep)
  end