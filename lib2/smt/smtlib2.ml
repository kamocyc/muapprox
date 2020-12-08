(* Parser for SmtLib2 *)
open Core open Core.Poly
open Ast
open Ast.Logic
open Fptprover
open Ast.Gather

open Parsexp
module Sexp = Ppx_sexp_conv_lib.Sexp


let sort_of_sexp = function
  | Sexp.Atom "Int" -> T_int.SInt
  | Sexp.Atom "Real" -> T_int.SReal
  | Sexp.Atom "Bool" -> T_bool.SBool
  | _ -> failwith "unknown sort"

(*
let of_params = List.map ~f:(function
    | Sexp.List [Sexp.Atom ident; sort] ->
      (Ident.Tvar ident, sort_of_sexp sort)
    | _ -> failwith "invalid param"
  )
*)

let of_params (acc: Variables.t) sexp =
  List.rev sexp |>
  List.fold_left ~f:(fun (acc, acc') -> function
      | Sexp.List [Sexp.Atom ident; sort] ->
        let e = (Ident.Tvar ident, sort_of_sexp sort) |> Variables.singleton in
        (Variables.union e acc, Variables.union e acc')
      | _ -> failwith "invalid param") ~init:(Variables.empty, acc)

let of_pred_sym = function
  | Sexp.Atom "=" -> T_bool.mk_eq
  | Sexp.Atom "<" -> T_int.mk_lt
  | Sexp.Atom ">" -> T_int.mk_gt
  | Sexp.Atom "<=" -> T_int.mk_leq
  | Sexp.Atom ">=" -> T_int.mk_geq
  | _ as op -> failwith @@ "parse error : unknown pred sym " ^ (Sexp.to_string_hum op)

let of_fun_sym = function
  | Sexp.Atom "+" -> T_int.mk_add
  | Sexp.Atom "-" -> T_int.mk_sub
  | Sexp.Atom "*" -> T_int.mk_mult
  | Sexp.Atom "/" | Sexp.Atom "div" -> T_int.mk_div
  | Sexp.Atom "mod" -> T_int.mk_mod
  | _ as op -> failwith @@ "parse error : unknown fun sym " ^ (Sexp.to_string_hum op)

let rec of_formula phi (tenv: Variables.t) (penv: PredVariables.t) = let open Formula in
  match phi with
  (* constant *)
  | Sexp.Atom "true" -> mk_atom (Atom.mk_true Dummy) Dummy
  | Sexp.Atom "false" -> mk_atom (Atom.mk_false Dummy) Dummy
  | Sexp.Atom ident -> begin
      match Variables.find_map tenv
              ~f:(fun (key, sort) -> if key = (Ident.Tvar ident) then Some(sort) else None) with
      (*      match Env.lookup_ (Ident.Tvar ident) tenv with *)
      | Some (sort) ->
        assert (sort = T_bool.SBool);
        let var = Term.mk_var (Ident.Tvar ident) sort Dummy in
        let atom = Atom.mk_app (Predicate.Psym T_bool.Eq) [var; T_bool.mk_bool (Atom.mk_true Dummy) Dummy] Dummy in
        mk_atom atom Dummy
      | None -> begin
          (*          let sorts = Env.lookup (Ident.Pvar ident) penv in *)
          let sorts = PredVariables.find_exn penv ~f:(fun (key, _) -> key = Ident.Pvar ident)
                      |> fun (_, sorts) -> sorts in
          assert (sorts = []);
          let pred = Predicate.mk_var (Ident.Pvar ident) sorts in
          mk_atom (Atom.mk_app pred [] Dummy) Dummy
        end
    end

  (* logical operation *)
  | Sexp.List [Sexp.Atom "not"; phi] ->
    mk_neg (of_formula phi tenv penv) Dummy
  | Sexp.List (Sexp.Atom "and" :: phis) ->
    let phis = List.rev_map phis ~f:(fun phi -> of_formula phi tenv penv) in
    and_of phis Dummy
  | Sexp.List (Sexp.Atom "or" :: phis) ->
    let phis = List.rev_map phis ~f:(fun phi -> of_formula phi tenv penv) in
    or_of phis Dummy
  | Sexp.List [Sexp.Atom "=>"; phi1; phi2] ->
    let phi1 = of_formula phi1 tenv penv in
    let phi2 = of_formula phi2 tenv penv in
    mk_imply phi1 phi2 Dummy

  (* binder *)
  | Sexp.List [Sexp.Atom "forall"; Sexp.List params; phi] ->
    let params, tenv = of_params tenv params in
    let phi = of_formula phi tenv penv in
    mk_forall (Variables.to_list params) phi Dummy
  | Sexp.List [Sexp.Atom "exists"; Sexp.List params; phi] ->
    let params, tenv = of_params tenv params in
    let phi = of_formula phi tenv penv in
    mk_exists (Variables.to_list params) phi Dummy

  (* predicate symbol application *)
  | Sexp.List [Sexp.Atom "=" as op; t1; t2]
  | Sexp.List [Sexp.Atom "<" as op; t1; t2]
  | Sexp.List [Sexp.Atom ">" as op; t1; t2]
  | Sexp.List [Sexp.Atom "<=" as op; t1; t2]
  | Sexp.List [Sexp.Atom ">=" as op; t1; t2] ->
    let t1 = of_term t1 tenv penv in
    let t2 = of_term t2 tenv penv in
    mk_atom ((of_pred_sym op) t1 t2 Dummy) Dummy

  (* let *)
  (* This case is only for adr_39_.smt2 which is ill-formed to chc-comp18 format. *)
  | Sexp.List [Sexp.Atom "let"; Sexp.List bounds; phi] when is_included_pvars tenv penv bounds ->
    let bounds = List.rev_map bounds ~f:(function
        | Sexp.List [Sexp.Atom ident; p] -> Ident.Pvar ident, of_formula p tenv penv
        | x -> failwith @@ "Invalid param: " ^ (Sexp.to_string_hum x)) in
    let penv = List.fold_left bounds ~init:penv
        ~f:(fun acc (var, _) -> let m = (PredVariables.singleton (var, [])) in
             PredVariables.union m acc) in

    let phi = of_formula phi tenv penv in
    List.fold_left ~init:phi ~f:(fun phi (pred, phi') -> Formula.subst_pred pred [] phi' phi) bounds

  | Sexp.List [Sexp.Atom "let"; Sexp.List bounds; phi] ->
    let bounds = List.rev_map bounds ~f:(function
        | Sexp.List [Sexp.Atom ident; t] -> Ident.Tvar ident, of_term t tenv penv
        | x -> failwith @@ "invalid param : " ^ (Sexp.to_string_hum x)) in
    let tenv = List.fold_left bounds ~init:tenv
        ~f:(fun tenv (var, _) -> let m = (Variables.singleton (var, T_bool.SBool)) in Variables.union m tenv) in
    let phi = of_formula phi tenv penv in
    (*    Printf.printf "original formula: %s\n\n" @@ Logic.Formula.str_of phi; *)
    Formula.subst (bounds |> Map.Poly.of_alist_exn) phi
  (*    |> (fun phi -> (Printf.printf "substed formula: %s" @@ Logic.Formula.str_of phi); phi)
        |> (fun _ -> assert false) *)

  | Sexp.List [Sexp.Atom "ite"; cond; then_; else_] ->
    let cond = of_term cond tenv penv in
    let then_ = of_term then_ tenv penv in
    let else_ = of_term else_ tenv penv in
    let t = T_bool.mk_if_then_else cond then_ else_ Dummy in
    Formula.mk_atom
      (Atom.mk_app (Predicate.Psym T_bool.Eq) [t; T_bool.mk_bool (Atom.mk_true Dummy) Dummy] Dummy)
      Dummy

  (* predicate variable application*)
  | Sexp.List (Sexp.Atom ident :: args) -> begin
      try
        let args = List.map args ~f:(fun t -> of_term t tenv penv) in
        let sorts = PredVariables.find_map penv
            ~f:(fun (key, sorts) -> if key = Ident.Pvar ident then Some(sorts) else None)
                    |> Util.Option.unwrap in
        (*        let sorts = Env.lookup (Ident.Pvar ident) penv in *)
        let pred = Predicate.mk_var (Ident.Pvar ident) sorts in
        mk_atom (Atom.mk_app pred args Dummy) Dummy
      with _ -> (failwith @@ "not found : " ^ ident ^ ", before " ^ (Sexp.to_string_hum @@ Sexp.List args)) end

  | _ as phi ->
    failwith @@ "parse error : " ^ (Sexp.to_string_hum phi)

and is_included_pvars tenv penv = function
  | [] -> false
  | (Sexp.List [Sexp.Atom _; t])::sexps ->
    let phi = of_formula t tenv penv in
    if (Logic.Formula.number_of_pvar_apps true phi) + (Logic.Formula.number_of_pvar_apps false phi) > 0 then true
    else is_included_pvars tenv penv sexps
  | x::_ -> failwith @@ "invalid bounds: " ^ (Sexp.to_string_hum x)

and of_term t tenv penv = let open Term in
  match t with
  | Sexp.Atom "true" -> T_bool.mk_bool (Atom.mk_true Dummy) Dummy
  | Sexp.Atom "false" -> T_bool.mk_bool (Atom.mk_false Dummy) Dummy
  | Sexp.Atom ident -> begin
      try
        (* case on integer constants *)
        (* TODO: this can not handle too big integer. use bigint *)
        T_int.mk_int (Bigint.of_string ident) Dummy
      with _ -> begin
          try
            (* case on float constants *)
            let _ = float_of_string ident in
            T_int.mk_real ident Dummy
          with _ -> begin
              (* case on others *)
              let sort = Variables.find_map tenv
                  ~f:(fun (Ident.Tvar key, sort) ->
                      if key = ident then Some sort else None) |> Util.Option.unwrap in
              (*              let sort = Env.lookup (Ident.Tvar ident) tenv in *)
              mk_var (Ident.Tvar ident) sort Dummy
            end
        end
    end

  | Sexp.List [Sexp.Atom "-"; t] ->
    let t = of_term t tenv penv in
    T_int.mk_unary_neg t Dummy
  | Sexp.List (Sexp.Atom "+" :: arg :: args) ->
    let arg = of_term arg tenv penv in
    List.fold_left args ~init:arg ~f:(fun acc t -> T_int.mk_add acc (of_term t tenv penv) Dummy)
(*
    let args = List.rev_map args ~f:(fun t -> of_term t tenv penv) in
    List.fold_left args ~init:arg ~f:(fun acc arg ->
        T_int.mk_add acc arg Dummy)*)

  | Sexp.List [Sexp.Atom "-" as op; t1; t2]
  | Sexp.List [Sexp.Atom "*" as op; t1; t2]
  | Sexp.List [Sexp.Atom "/" as op; t1; t2]
  | Sexp.List [Sexp.Atom "div" as op; t1; t2]
  | Sexp.List [Sexp.Atom "mod" as op; t1; t2] ->
    let t1 = of_term t1 tenv penv in
    let t2 = of_term t2 tenv penv in
    (of_fun_sym op) t1 t2 Dummy

  | Sexp.List [Sexp.Atom "ite"; cond; then_; else_] ->
    let cond = of_term cond tenv penv in
    let then_ = of_term then_ tenv penv in
    let else_ = of_term else_ tenv penv in
    T_bool.mk_if_then_else  cond then_ else_ Dummy

  (* let-expressions as term *)
  | Sexp.List [Sexp.Atom "let"; Sexp.List bounds; _] when is_included_pvars tenv penv bounds ->
    failwith "Invalid let-expressions (It is not allowed to use let-term binding predicate applications into some name.)"

  | Sexp.List [Sexp.Atom "let"; Sexp.List bounds; body] ->
    let bounds = List.rev_map bounds ~f:(function
        | Sexp.List [Sexp.Atom ident; t] -> Ident.Tvar ident, of_term t tenv penv
        | x -> failwith @@ "invalid param : " ^ (Sexp.to_string_hum x)) in
    let tenv = List.fold_left bounds ~init:tenv
        ~f:(fun tenv (var, _) -> let m = (Variables.singleton (var, T_bool.SBool)) in Variables.union m tenv) in
    let body = of_term body tenv penv in
    Term.subst (bounds |> Map.Poly.of_alist_exn) body

  | t ->
    let phi = of_formula t tenv penv in
    T_bool.mk_formula phi Dummy

let str_of_tenv tenv =
  String.concat ~sep:", "
  @@ List.map
    ~f:(fun (tvar, sort) ->
        Printf.sprintf "(%s: %s)"(Ident.name_of_tvar tvar) (Convert.Printer.str_of_sort sort)
      )
  @@ Env.entries tenv

let str_of_penv (penv: PredVariables.t) =
  String.concat ~sep:", "
  @@ List.map ~f:(fun (ident, sorts) ->
      Printf.sprintf "(%s: %s)" (Ident.name_of_pvar ident)
      @@ String.concat ~sep:" -> " (List.map ~f:(fun sort -> Convert.Printer.str_of_sort sort) sorts)
    ) (PredVariables.to_list penv)
  (*
  String.concat ~sep:", "
  @@ List.map
    ~f:(fun (pvar, sorts) ->
        Printf.sprintf "(%s: %s)" (Ident.name_of_pvar pvar)
        @@ String.concat ~sep:" -> "
        @@ List.map ~f:(fun sort -> Convert.Printer.str_of_sort sort)
          (sorts @ [T_bool.SBool])
      )
  @@ Env.entries penv
*)
let restrict_head bounds args fml =
  List.fold_left args
    ~init:(bounds, [], fml)
    ~f:(fun (bounds, args, fml) arg ->
        let arg_sort: Sort.t = AstUtil.sort_of_term [] arg in
        let new_ident: Ident.tvar = Ident.mk_fresh_head_arg () in
        let new_arg: Term.t = Term.mk_var new_ident arg_sort Dummy in
        let bounds = (new_ident, arg_sort) :: bounds in
        let args = new_arg :: args in
        let fml = Formula.mk_and
            fml
            (Formula.mk_atom
               (Atom.mk_app
                  (Predicate.Psym T_bool.Eq)
                  [
                    new_arg;
                    arg;
                  ]
                  Dummy)
               Dummy)
            Dummy in
        bounds, args, fml)

let smt_of_formula acc tenv (penv: PredVariables.t) =
  (* output for debugging *)
  Debug.print "==============================";
  Debug.print "lib-smt2 --> formula";
  Debug.print "==============================";
  Debug.print @@ Printf.sprintf "tenv: %s" @@ str_of_tenv tenv;
  Debug.print @@ Printf.sprintf "penv: %s" @@ str_of_penv penv;
  Debug.print @@ Printf.sprintf "assertions:\n%s\n"
  @@ String.concat ~sep:"\n"
  @@ List.map
    ~f:(fun fml -> Convert.PrinterHum.str_of_formula fml) acc;
  (* make tvars of args of functions *)
  let tvars_of_functions = Env.update
      (List.map
         ~f:(fun (pvar, sorts) ->
             pvar, List.mapi
               ~f:(fun i _ ->
                   Ident.Tvar ("#arg" ^ (string_of_int i))
                 ) sorts
           )
       @@ PredVariables.to_list penv(* Env.entries penv *))
      Env.empty
  in
  (* make body of functions and entrypoint *)
  let rec rep entry fenv = function
    | [] ->
      Formula.mk_neg
        (Formula.mk_letrec
           (List.map
              ~f:(fun pvar ->
                  Predicate.Mu,
                  pvar,
                  List.zip_exn (Env.lookup pvar tvars_of_functions)
                    (PredVariables.find_map penv
                       ~f:(fun (key, sorts) -> if key = pvar then Some sorts else None) |> Util.Option.unwrap)(*Env.lookup pvar penv*),
                  Formula.or_of (Env.lookup pvar fenv) Dummy
                ) @@ (PredVariables.to_list penv |> List.map ~f:(fun (key, _) -> key)) (*Env.keys penv*))
           (Formula.or_of entry Dummy)
           Dummy)
        Dummy
    | fml :: tail ->
      let bounds, fml, info_forall = Formula.let_forall_or_formula fml in
      let fml, fml', _ = Formula.let_imply fml in
      let atom, _ = Formula.let_atom fml' in
      if Atom.is_false atom then
        rep
          (Formula.mk_exists_if_bounded
             bounds fml info_forall
           :: entry) fenv tail
      else
        let pred, args, _ = Atom.let_app atom in
        let bounds, args, fml = restrict_head bounds args fml in
        if Predicate.is_psym pred then
          let fml = Formula.mk_neg
              (Formula.mk_imply fml fml' Dummy)
              Dummy in
          rep
            (Formula.mk_exists_if_bounded
               bounds fml info_forall
             :: entry) fenv tail
        else
          let pvar, _ = Predicate.let_var pred in
          (* replace bounded tvars with tvars of args *)
          let fml = Formula.subst
              (List.map ~f:(fun (cur_arg, new_tvar) ->
                   let cur_tvar, sort, info = Term.let_var cur_arg in
                   cur_tvar, Term.mk_var new_tvar sort info
                 ) @@ List.zip_exn args @@ Env.lookup pvar tvars_of_functions
               |> Map.Poly.of_alist_exn) fml
          in
          let replaced_tvars = List.map
              ~f:(fun arg -> let tvar, _, _ = Term.let_var arg in tvar) args
          in
          let bounds = List.filter
              ~f: (fun (tvar, _) -> not @@ List.exists replaced_tvars ~f:(fun tvar' -> tvar = tvar'))
              bounds
          in
          let fml = Formula.mk_exists_if_bounded
              bounds
              fml
              info_forall
          in
          rep entry (Env.update [pvar, fml :: (Env.lookup pvar fenv)] fenv) tail
  in
  rep [] (Env.update (List.map ~f:(fun (pvar, _) -> pvar, []) @@ PredVariables.to_list penv(*Env.entries penv*)) Env.empty) acc

let rec toplevel acc (tenv:Variables.t) (penv:PredVariables.t) = function
  | [] -> Ok (acc, tenv, penv) (*(smt_of_formula acc tenv penv)*)
  | (Sexp.List [Sexp.Atom "set-logic"; Sexp.Atom "HORN"]) :: es
  | (Sexp.List (Sexp.Atom "set-info" :: _)) :: es
  | (Sexp.List [Sexp.Atom "check-sat"]) :: es
  | (Sexp.List [Sexp.Atom "exit"]) :: es
    -> toplevel acc tenv penv es
  | (Sexp.List [Sexp.Atom "declare-fun"; Sexp.Atom ident; Sexp.List param_tys; Sexp.Atom "Bool"]) :: es ->
    let param_type = List.map param_tys ~f:sort_of_sexp in
    let penv = PredVariables.union (PredVariables.singleton (Ident.Pvar ident, param_type)) penv in
    (*    let penv = (Ident.Pvar ident, param_type) :: penv in *)
    toplevel acc tenv penv es
  | (Sexp.List [Sexp.Atom "assert"; phi]) :: es ->
    let phi = of_formula phi tenv penv in
    toplevel (phi :: acc) tenv penv es
  | _ as x -> failwith @@ "parse error : " ^ (Sexp.to_string_hum @@ Sexp.List x)

let toplevel = toplevel [] (Variables.empty) (PredVariables.empty)

let from_file filename =
  let open Util in
  let src = In_channel.read_all filename in
  match Many.parse_string src with
  | Ok (sexps) ->
    toplevel sexps
    |> Result.and_then (fun (acc, tenv, penv) -> Ok (smt_of_formula acc (Variables.to_list tenv) penv))
  | Error err ->
    let pos = Parse_error.position err in
    let msg = Parse_error.message err in
    Error (Printf.sprintf "at line %d, col %d: %s" pos.line pos.col msg)

let raw_smt_from_file filename =
  let src = In_channel.read_all filename in
  match Many.parse_string src with
  | Ok (sexps) -> toplevel sexps
  | Error err ->
    let pos = Parse_error.position err in
    let msg = Parse_error.message err in
    Error (Printf.sprintf "at line %d, col %d: %s" pos.line pos.col msg)
