open Common_type
open Hflmc2_syntax
module R = Program_raw

module Env = Manipulate.Env_no_value

type tv_expression = R.ptype Id.t R.raw_expression_gen
[@@deriving eq,ord,show]

type tv_function = R.ptype Id.t R.raw_function_gen
[@@deriving eq,ord,show]

type tv_program = R.ptype Id.t R.raw_program_gen
[@@deriving eq,ord,show]

let get_type = Trans_raw_program.get_type

let show_raw_program_sub p =
  let rec go p = match p with
    | R.PUnit -> "()"
    | PVar s -> Id.to_string ~without_id:true s
    | PIf (p, p1, p2) -> "if " ^ go p ^ " then (" ^ go p1 ^ ") else (" ^ go p2 ^ ")"
    | PEvent (pe, p) -> "event " ^ pe ^ "; " ^ go p
    | PNonDet (p1, p2, e) ->
      "if" ^ (match e with None -> "" | Some e -> " <" ^ e ^ ">") ^ " * then ("  ^ go p1 ^ ") else (" ^ go p2 ^ ")"
    | PApp (p1, p2) -> "(" ^ go p1 ^ " " ^ go p2 ^ ")"
    | AInt i -> string_of_int i
    | AOp (op, [arg1; arg2]) -> "(" ^ go arg1 ^ " " ^ Print_syntax.show_op op ^ " " ^ go arg2 ^ ")"
    | AOp _ -> failwith "show_program: go_arith"
    | ANonDet e -> (match e with None -> "" | Some e -> " <" ^ e ^ ">") ^ "*"
    | Pred (op, [arg1; arg2]) -> "(" ^ go arg1 ^ " " ^ Print_syntax.show_pred op ^ " " ^ go arg2 ^ ")"
    | Pred _ -> failwith "show_program: go_predicate"
    | And (p1, p2) -> "(" ^ go p1 ^ " && " ^ go p2 ^ ")"
    | Or (p1, p2) -> "(" ^ go p1 ^ " || " ^ go p2 ^ ")"
    | Bool b -> string_of_bool b
    | PLet (x, p1, p2) ->
      "(let (" ^ Id.to_string ~without_id:true x ^ " : " ^ (R.show_ptype x.ty) ^ ") = " ^ go p1 ^ " in " ^ go p2 ^ ")"
    | PLambda (xs, p1) ->
      "(\\" ^ (List.map (fun x -> "(" ^ Id.to_string ~without_id:true x ^ " : " ^ R.show_ptype x.ty ^ ")") xs |> String.concat " ") ^ ". " ^ go p1 ^ ")"
  in
  go p

let show_raw_program program =
  let (entry, rules) = List.partition (fun rule -> rule.R.var.Hflmc2_syntax.Id.name = "") program in
  "let () = " ^ show_raw_program_sub (List.hd entry).R.body ^ "\n" ^
  (
    List.map (fun {R.var; args; body} ->
      let rec b = function | R.TFunc (_, t) -> b t | t -> t in
      "let " ^ Id.to_string ~without_id:true var ^ " " ^
        (String.concat " " (List.map (fun {Id.name; ty} -> "(" ^ name ^ ": " ^ R.show_ptype ty ^ ")") args)) ^
        " : " ^ R.show_ptype (b var.ty) ^
        " = " ^ show_raw_program_sub body
    ) rules |>
    String.concat "\n"
  )

(* 型情報のためにunifyする必要 *)
(*  *)

let id_gen ty =
  let open Hflmc2_syntax in
  let id = Id.gen () in
  { id with
    name = "x" ^ string_of_int id.id;
    ty = ty
  }

let rec to_cps_type_sub = function
  | R.TInt -> R.TInt
  |   TBool -> TBool
  |   TUnit -> TUnit
  |   TFunc (p1, p2) ->
    TFunc (
      to_cps_type_sub p1,
      TFunc (
        TFunc (
          to_cps_type_sub p2,
          TCPS
        ),
        TCPS
      )
    )
  | TVar id -> assert false
  | TCPS -> assert false
  
let to_cps_type expr =
  let ty = to_cps_type_sub expr in
  R.TFunc (
    R.TFunc (ty, TCPS),
    TCPS
  )

  
    
let trans (phi : tv_expression) : tv_expression =
  let rec go_prog (phi : tv_expression) : tv_expression =
    match phi with
    | R.PUnit ->
      let ty = R.TFunc (TUnit, TCPS) in
      let id = id_gen ty in
      R.PLambda (
        [id],
        PApp (PVar id, PUnit)
      )
    | PVar s -> begin
      let ty =
        match s.ty with
        | TInt -> to_cps_type_sub s.ty
        | _ -> to_cps_type s.ty in
      let s = { s with ty = ty } in
      let x = R.TFunc (ty, TCPS) in
      let id = id_gen x in
      PLambda (
        [id],
        PApp (PVar id, PVar s)
      )
    end
    | PLambda (xs, expr) ->
      let ty = get_type phi in
      let tyk = R.TFunc (ty, TCPS) in
      let id = id_gen tyk in
      PLambda (
        [id],
        PApp (PVar id, PLambda (xs, go_prog expr))
      )
    | PApp (e1, e2) ->
      let ty = get_type phi in
      let tyk = R.TFunc (TFunc (ty, TCPS), TCPS) in
      let tyx = get_type e2 in
      print_endline @@ R.show_ptype tyx;
      let tyf = R.TFunc (tyx, TFunc (tyk, TCPS)) in
      let id_k = id_gen tyk in
      let id_f = id_gen tyf in
      let id_x = id_gen tyx in
      let e1 = go_prog e1 in
      let e2 =
        match tyx with
        | TInt -> go_arith e2
        | _ -> go_prog e2
      in
      PLambda (
        [id_k],
        PApp (
          e1,
          PLambda (
            [id_f],
            PApp (
              e2,
              PLambda (
                [id_x],
                PApp (
                  PApp (
                    PVar id_f,
                    PVar id_x
                  ),
                  PVar id_k
                )
              )
            )
          )
        )
      )
    | PIf (e1, e2, e3) ->
      let tyk = R.TFunc (TFunc (TUnit, TCPS), TCPS) in
      let id_k = id_gen tyk in
      let tyx = R.TBool in
      let id_x = id_gen tyx in
      let e1 = go_pred e1 in
      let e2 = go_prog e2 in
      let e3 = go_prog e3 in
      PLambda (
        [id_k],
        PApp (
          e1,
          PLambda (
            [id_x],
            PIf (
              PVar id_x,
              PApp (
                e2,
                PVar id_k
              ),
              PApp (
                e3,
                PVar id_k
              )
            )
          )
        )
      )
    | PEvent (e, e1) ->
      let ty = get_type e1 in
      let tyk = R.TFunc (ty, TCPS) in
      let id_k = id_gen tyk in
      PLambda (
        [id_k],
        PEvent (e, PApp (go_prog e1, PVar id_k))
      )
    | PNonDet (p1, p2, e) ->
      let ty = get_type p1 in
      let tyk = R.TFunc (ty, TCPS) in
      let id_k = id_gen tyk in
      PLambda (
        [id_k],
        PNonDet (
          PApp (go_prog p1, PVar id_k),
          PApp (go_prog p2, PVar id_k),
          e
        )
      )
    | PLet (x, p1, p2) ->
      (* letはapplicationに変換 *)
      go_prog
        (PApp (
          PLambda (
            [x],
            p2
          ),
          p1
        ))
    | Pred _ | And _ | Or _ | Bool _ -> go_pred phi
    | AOp _ | AInt _ | ANonDet _ -> go_arith phi
    and go_pred phi =
      let rec go phi =
        match phi with
        | R.Pred (op, ps) -> true
        | And (p1, p2) -> go p1 && go p2
        | Or (p1, p2) -> go p1 && go p2
        | Bool b -> true
        | _ -> false
      in
      print_endline @@ show_tv_expression phi;
      assert (go phi);
      let tyk = R.TFunc (TBool, TCPS) in
      let id_k = id_gen tyk in
      PLambda (
        [id_k],
        PApp (
          PVar id_k,
          phi
        )
      )
    (* match phi with
      | R.Pred (o, [e1; e2]) ->
        let ty = R.TBool in
        let tyk = R.TFunc (ty, TCPS) in
        let id_k = id_gen tyk in
        PLambda (
          [id_k],
          PApp (
            PVar id_k,
            Pred (o, [e1; e2])
          )
        )
      | And (p1, p2) ->
        
      | Or (p1, p2) -> *)
    and go_arith phi =
      let rec go phi =
        match phi with
        | R.AOp (op, ps) -> List.for_all go ps
        | AInt i -> true
        | PVar v -> true
        | ANonDet e -> true
        | _ -> false
      in
      print_endline @@ show_tv_expression phi;
      assert (go phi);
      let tyk = R.TFunc (TInt, TCPS) in
      let id_k = id_gen tyk in
      PLambda (
        [id_k],
        PApp (
          PVar id_k,
          phi
        )
      )
    in
    go_prog phi

let generate_constraints (raw : tv_program) : (R.ptype * R.ptype) list =
  let open R in
  let rec gen (env : R.ptype Env.t) (raw : tv_expression):
      ptype * (ptype * ptype) list
       = match raw with
    | PIf (p1, p2, p3) ->
      let t1, c1 = gen env p1 in
      let t2, c2 = gen env p2 in
      let t3, c3 = gen env p3 in
      (t2, [(t1, TBool); (t2, t3)] @ c1 @ c2 @ c3)
    | PLambda (args, body) ->
      let t, c = gen (Env.update args env) body in
      let rec go base ls = match ls with
        | [] -> base
        | x::xs -> TFunc (x.Id.ty, go base xs) in
      (go t args, c)
    | PApp (p1, p2) ->
      let t1, c1 = gen env p1 in
      let t2, c2 = gen env p2 in
      let tvar = Id.gen () in
      (TVar tvar, (t1, TFunc (t2, TVar tvar)) :: c1 @ c2)
    | PUnit -> (TUnit, [])
    | AInt _ -> (TInt, [])
    | Bool _ -> (TBool, [])
    | ANonDet _ -> (TInt, [])
    | PVar v ->
      let id = Env.lookup v env in
      (id.ty, [])
    | PLet (x, p1, p2) ->
      let t1, c1 = gen env p1 in
      let t2, c2 = gen (Env.update [x] env) p2 in
      (t2, (x.ty, t1) :: c1 @ c2)
    | PEvent (_, p) ->
      let t, c = gen env p in
      (t, c)
    | PNonDet (p1, p2, _) ->
      (* non-deterministic branch should have unit type *)
      let t1, c1 = gen env p1 in
      let t2, c2 = gen env p2 in
      (t1, (t1, t2) :: c1 @ c2)
    | AOp (e, ps) ->
      let results = List.map (gen env) ps in
      let tys, cs = List.split results in
      (TInt, (List.map (fun ty -> (TInt, ty)) tys) @ (List.flatten cs))
    | Pred (e, ps) ->
      let results = List.map (gen env) ps in
      let tys, cs = List.split results in
      (TBool, (List.map (fun ty -> (TInt, ty)) tys) @ (List.flatten cs))
    | And (p1, p2) ->
      let t1, c1 = gen env p1 in
      let t2, c2 = gen env p2 in
      (TBool, (TBool, t1) :: (TBool, t2) :: c1 @ c2)
    | Or (p1, p2) ->
      let t1, c1 = gen env p1 in
      let t2, c2 = gen env p2 in
      (TBool, (TBool, t1) :: (TBool, t2) :: c1 @ c2) in
  let global_env = List.map (fun {var} -> var) raw in
  let constraints =
    List.map
      (fun ({var; args; body} : tv_function) ->
        let rec b = function TFunc (_, t) -> b t | t -> t in
        let (ty, c) = gen (Env.update args (Env.create global_env)) body in
        ((b var.ty, ty)) :: c
      )
      raw
    |> List.flatten in
  constraints

let infer_type (raw : tv_program) =
  (* print_endline @@ show_tv_program raw; *)
  let constraints = generate_constraints raw in
  let substitution = Trans_raw_program.unify constraints in
  let raw = Trans_raw_program.subst_program raw substitution in
  print_endline @@ show_tv_program raw;
  raw

let trans1 program =
  let open Trans_raw_program in
  let open Hflmc2_syntax in
  let pred_args =
    let preds =
      List.map (fun {R.var} -> var) program |> List.filter (fun a -> a.Id.name <> "")
      |> Env.create in
    List.map (fun {R.var; args; body} ->
      let base_name = if var.Id.name = "" then None else Some var.Id.name in
      let body, new_rules = lambda_lift ?base_name preds (Env.create args) body in
      {R.var; args; body}::new_rules
    ) program
    |> List.flatten in
  let program_funcs =
    let preds =
      List.map (fun {R.var} ->
        try
          { var with Id.ty = to_ty var.Id.ty }
        with ETVar -> failwith @@ "type variable in " ^ var.name ^ " (maybe unused predicate?)"
      ) pred_args |> List.filter (fun a -> a.Id.name <> "")
      |> Env.create in
    List.map (
      fun {R.var; args; body} ->
        let var = { var with Id.ty = to_ty var.Id.ty } in
        let args = List.map (fun id -> {id with Id.ty = to_argty id.Id.ty}) args in
        let body = convert body (Env.create args) preds in
        {Program.var; args; body}
    ) pred_args in
  match program_funcs |> List.partition (fun {Program.var;_} -> var.Id.name = "") with
  | [entry], xs ->
    let move_main_subs_tofirst xs =
      let firsts, seconds = List.partition (fun {Program.var} -> has_prefix var.name "lam_") xs in
      firsts @ seconds in
    entry.body, move_main_subs_tofirst xs
  | _ -> failwith "convert_all"

let rec free_vars = function
  | R.PVar x -> [x]
  | PUnit -> []
  | PApp (e1, e2) -> free_vars e1 @ free_vars e2
  | PLambda (xs, e1) -> List.filter (fun x' -> not @@ List.exists (Id.eq x') xs) (free_vars e1)
  | PIf (p, p1, p2) ->
    free_vars p @ free_vars p1 @ free_vars p2
  | PEvent (_, p) -> free_vars p
  | PNonDet (p1, p2, _) -> free_vars p1 @ free_vars p2
  
  | Pred (_, xs) -> List.map free_vars xs |> List.flatten
  | And (p1, p2) -> free_vars p1 @ free_vars p2
  | Or (p1, p2) -> free_vars p1 @ free_vars p2
  | Bool _ -> []
  
  | AOp (_, xs) -> List.map free_vars xs |> List.flatten
  | AInt _ -> []
  | ANonDet _ -> []
  | PLet (x, e1, e2) -> free_vars e1 @ (List.filter (fun x' -> not @@ (Id.eq x' x)) @@ free_vars e2)  

let rec subst expr1 (v, expr2) =
  match expr1 with
  | R.PVar x when Id.eq x v -> expr2
  | PVar x -> R.PVar x
  | PApp (e1, e2) ->
    PApp (
      subst e1 (v, expr2),
      subst e2 (v, expr2)
    )
  | PLambda (xs, e1) when List.exists (Id.eq v) xs -> PLambda (xs, e1)
  | PLambda (xs, e1) -> begin
    let frees = free_vars expr2 in
    let (args, e1) = List.fold_left
      (fun (args, e1) x ->
        match List.find_opt (fun x' -> x' = x) frees with
        | Some _ ->
          (* capture avoiding *)
          let new_id = id_gen x.ty in
          new_id :: args, subst e1 (x, PVar new_id)
        | None -> x :: args, e1
      )
      ([], e1)
      xs in
    PLambda (List.rev args, subst e1 (v, expr2))
  end
  | _ -> assert false
      

let beta_reduce expr =
  let rec go expr = match expr with
    (* 複数引数のとき？ -> CPS変換では1引数しか現れないので、複数の引数は対応しない *)
    | R.PApp (
      PLambda (
        [param],
        body
      ),
      arg
    ) ->
      (* subst *)
      subst body (param, arg)
    | PUnit | PVar _ -> R.PUnit
    | PIf (p, p1, p2) ->
      PIf (p, go p1, go p2)
    | PEvent (e, p) ->
      PEvent (e, go p)
    | PNonDet (p1, p2, e) ->
      PNonDet (go p1, go p2, e)
    | PApp (p1, p2) -> begin
      match get_type p2 with
      | TInt -> 
        PApp (go p1, p2)
      | _ ->
        PApp (go p1, go p2)
    end
    | _ -> assert false
  in
  go expr 

module T = Trans_raw_program

let trans2 program =
  let tv_program = T.assign_id true program |> infer_type in
  print_endline "typed";
  print_endline @@ Trans_raw_program.show_tv_program tv_program;
  print_endline @@ show_raw_program tv_program;
  let tv_program =
    tv_program
    |> List.map (fun func ->
      let body = trans func.R.body in
      if func.R.var.Hflmc2_syntax.Id.name = "" then begin
        let id_k = id_gen (R.TFunc (R.TFunc (TUnit, TCPS), TCPS)) in
        let body = R.PApp (body, PLambda ([id_k], R.PUnit)) in
        { func with body }
      end else begin
        match body with
        | PLambda (
          [x],
          body
        ) ->
          let body = T.convert_let body in
          { R.args = func.args @ [x]; var = func.var; body = body }
        | _ -> assert false
      end
    ) in
  print_endline "before reduce";
  print_endline @@ Trans_raw_program.show_tv_program tv_program;
  print_endline @@ show_raw_program tv_program;
  (* let program = trans1 tv_program in *)
  
  let tv_program =
    tv_program
    |> List.map (fun func ->
      let body = beta_reduce func.R.body in
      { func with R.body = body }
    ) in
  print_endline "after reduce";
  print_endline @@ Trans_raw_program.show_tv_program tv_program;
  print_endline @@ show_raw_program tv_program;
  (* let program = trans1 tv_program in *)
  (* print_endline @@ Print_syntax.show_program program; *)
  tv_program
