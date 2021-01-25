module Hflz = Hflmc2_syntax.Hflz
module Id = Hflmc2_syntax.Id
module Type = Hflmc2_syntax.Type
module Arith = Hflmc2_syntax.Arith
  
let find_id_opt key assoc = List.find_opt (fun (k, _) -> Id.eq k key) assoc
let find_id key assoc = match find_id_opt key assoc with None -> raise Not_found | Some x -> x
let id x = x

let lift_id id =
  { id with Id.ty = Type.TySigma id.Id.ty}

let unlift_id id =
  { id with Id.ty = Type.unsafe_unlift id.Id.ty}

(* type 'ty hflz_ =
  | Bool   of bool
  | Var    of 'ty Id.t
  | Or     of 'ty hflz_ list
  | And    of 'ty hflz_ list
  | Abs    of 'ty Type.arg Id.t list * 'ty hflz_
  | Forall of 'ty Type.arg Id.t list * 'ty hflz_
  | Exists of 'ty Type.arg Id.t list * 'ty hflz_
  | App    of 'ty hflz_ * 'ty hflz_
  (* constructers only for hflz *)
  | Arith  of Arith.t
  | Pred   of Hflmc2_syntax.Formula.pred * Arith.t list *)
  
let assign_serial_to_vars gen env (phi : Type.simple_ty Hflz.t) =
  let rec go env (phi : 'a Hflz.t) : 'a Hflz.t = match phi with
    | And (phi1, phi2) -> And (go env phi1, go env phi2)
    | Or (phi1, phi2) -> Or (go env phi1, go env phi2)
    | App (phi1, phi2) -> App (go env phi1, go env phi2)
    | Abs (x, phi1) -> begin
      let gened_id = gen x.ty in
      let env = (x, gened_id)::env in
      Abs (gened_id, go env phi1)
    end
    | Forall (x, phi1) -> begin
      let gened_id = gen x.ty in
      let env = (x, gened_id)::env in
      Forall (gened_id, go env phi1)
    end
    | Exists (x, phi1) -> begin
      let gened_id = gen x.ty in
      let env = (x, gened_id)::env in
      Exists (gened_id, go env phi1)
    end
    | Arith (psi1) -> Arith (go_arith env psi1)
    | Pred (p, psis) -> Pred (p, List.map (go_arith env) psis)
    | Bool _-> phi
    | Var v -> begin
      match find_id_opt v env with
      | Some (_, v') ->
        Var (unlift_id v')
      | None -> failwith @@ "(assign_serial_to_vars, go) unbounded variable (" ^ v.name ^ ")"
    end 
  and go_arith env (psi : Arith.t) : Arith.t = match psi with
    | Int i -> Int i
    | Var v -> begin
      match find_id_opt v env with
      | Some (_, v') -> begin
        assert (v'.ty = TyInt);
        Var ({ v' with ty = `Int})
      end
      | None -> failwith @@ "(assign_serial_to_vars, go_arith) unbounded variable (" ^ v.name ^ ")"
    end
    | Op (op, ariths) -> Op (op, List.map (go_arith env) ariths) in
  go env phi
  
let assign_serial_to_vars_hes ((entry, rules) : Type.simple_ty Hflz.hes) =
  let counter = ref 0 in
  let gen ty =
    counter := !counter + 1;
    { Id.name = "x" ^ (string_of_int !counter); id = !counter; ty = ty } in
  let env = List.map (fun rule -> (lift_id rule.Hflz.var, gen (Type.TySigma rule.Hflz.var.ty))) rules in
  let entry = assign_serial_to_vars gen env entry in
  let rules =
    List.map (fun rule -> {
      Hflz.var = unlift_id (find_id rule.Hflz.var env |> snd);
      fix = rule.fix;
      body = assign_serial_to_vars gen env rule.body}) rules in
  entry, rules

let check_equal phi1 phi2 =
  let cp path constr dir = (constr ^ " " ^ dir) :: path in
  let error_path = ref "" in
  let set_path_if_false path b mes =
    if not b then error_path := (String.concat ", " (List.rev path)) ^ ": " ^ mes;
    b in
  let rec go path phi1 phi2 = match phi1, phi2 with
    | Hflz.Bool b1, Hflz.Bool b2 -> set_path_if_false path (b1 = b2) "Bool"
    | Or (phi_l1, phi_r1), Or (phi_l2, phi_r2) -> (go (cp path "Or" "Left") phi_l1 phi_l2) && (go (cp path "Or" "Right") phi_r1 phi_r2)
    | And (phi_l1, phi_r1), And (phi_l2, phi_r2) -> (go (cp path "And" "Left") phi_l1 phi_l2) && (go (cp path "And" "Right") phi_r1 phi_r2)
    | App (phi_l1, phi_r1), App (phi_l2, phi_r2) -> (go (cp path "App" "Left") phi_l1 phi_l2) && (go (cp path "App" "Right") phi_r1 phi_r2)
    | Var id1, Var id2 -> set_path_if_false path (Id.eq id1 id2) "Var"
    | Abs (x1, phi1), Abs(x2, phi2) -> (set_path_if_false path (Id.eq x1 x2) "Abs") && (go (cp path "Abs" "_") phi1 phi2)
    | Forall (x1, phi1), Forall (x2, phi2) -> (set_path_if_false path (Id.eq x1 x2) "Forall") && (go (cp path "Forall" "_") phi1 phi2)
    | Exists (x1, phi1), Exists (x2, phi2) -> (set_path_if_false path (Id.eq x1 x2) "Exists") && (go (cp path "Exists" "_") phi1 phi2)
    | Arith psi1, Arith psi2 -> go_arith (cp path "Arith" "_") psi1 psi2
    | Pred (p1, ariths1), Pred (p2, ariths2) ->
      set_path_if_false path (p1 = p2) "Pred" &&
      set_path_if_false path (List.length ariths1 = List.length ariths2) "Pred Args Length" &&
      agg_ariths path "Pred" ariths1 ariths2
    | _ -> set_path_if_false path false "Other"
  and go_arith path phi1 phi2 = match phi1, phi2 with
    | Arith.Int i1, Arith.Int i2 -> set_path_if_false path (i1 = i2) "Arith Int"
    | Var v1, Var v2 -> set_path_if_false path (Id.eq v1 v2) "Arith Var"
    | Op (op1, ariths1), Op (op2, ariths2) ->
      set_path_if_false path (op1 = op2) "Arith Op" &&
      set_path_if_false path (List.length ariths1 = List.length ariths2) "Arith Op Args Length" && 
      agg_ariths path "Op" ariths1 ariths2
    | _ -> set_path_if_false path false "Arith.Other" 
  and agg_ariths path path_append ariths1 ariths2 =
    ariths1 |>
    List.mapi (fun i arith1 -> go_arith (cp path path_append (string_of_int i)) arith1 (List.nth ariths2 i)) |>
    List.for_all id
  in
  let res = go [] phi1 phi2 in
  (res, !error_path)

let check_equal_hes hes1 hes2 =
  if List.length hes1 <> List.length hes2 then (false, "hes List length mismatch")
  else
    hes1 |>
    List.mapi (fun i rule1 ->
      let rule2 = List.nth hes2 i in
      if not @@ Id.eq rule1.Hflz.var rule2.Hflz.var then (false, "Not equal: Pred id")
      else (if rule1.Hflz.fix <> rule2.Hflz.fix then (false, "Not equal: Fixpoint") else let (r, m) = check_equal rule1.Hflz.body rule2.Hflz.body in (r, rule1.var.name ^ ": " ^ m))) |>
    List.fold_left (fun (b, m) (b', m') -> if b then (b', m') else (b, m)) (true, "")
