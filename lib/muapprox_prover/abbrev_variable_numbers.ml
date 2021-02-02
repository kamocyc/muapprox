module Hflz = Hflmc2_syntax.Hflz
module Id = Hflmc2_syntax.Id
module Type = Hflmc2_syntax.Type
module Arith = Hflmc2_syntax.Arith

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

let extract_name name =
  let reg = Str.regexp "\\([A-Za-z_'#0-9]*[A-Za-z_'#]\\)\\d*" in
  ignore @@ Str.search_forward reg name 0;
  let name = Str.matched_group 1 name in
  (* print_endline @@ "name=" ^ name; *)
  name

let next_name name =
  let reg = Str.regexp "\\([A-Za-z_'#0-9]*[A-Za-z_'#]\\)\\(\\d*\\)" in
  ignore @@ Str.search_forward reg name 0;
  let name' = Str.matched_group 1 name in
  let num = Str.matched_group 2 name in
  (* print_endline @@ "name=" ^ name'; *)
  let next_num = if num = "" then "1" else string_of_int (int_of_string num + 1) in
  name ^ next_num

let find_by_name key env = List.find_opt (fun (orig_id, conv_id, basename) -> basename = key) env
let find_id_opt id env = List.find_opt (fun (orig_id, conv_id, basename) -> Id.eq orig_id id) env

let get_new_id env x =
  let basename = extract_name x.Id.name in
  let new_id =
    match find_by_name basename env with
    | None -> {x with name = basename}
    | Some (_, n, _) -> {x with name = next_name n.Id.name} in
  new_id, basename
  
let abbrev_variable_numbers env (phi : Type.simple_ty Hflz.t) =
  let rec go env (phi : 'a Hflz.t) : 'a Hflz.t = match phi with
    | And (phi1, phi2) -> And (go env phi1, go env phi2)
    | Or (phi1, phi2) -> Or (go env phi1, go env phi2)
    | App (phi1, phi2) -> App (go env phi1, go env phi2)
    | Abs (x, phi1) -> begin
      let new_id, basename = get_new_id env x in
      Abs(new_id, go ((x, new_id, basename)::env) phi1)
    end
    | Forall (x, phi1) -> begin
      let new_id, basename = get_new_id env x in
      Forall(new_id, go ((x, new_id, basename)::env) phi1)
    end
    | Exists (x, phi1) -> begin
      let new_id, basename = get_new_id env x in
      Exists(new_id, go ((x, new_id, basename)::env) phi1)
    end
    | Arith (psi1) -> Arith (go_arith env psi1)
    | Pred (p, psis) -> Pred (p, List.map (go_arith env) psis)
    | Bool _-> phi
    | Var v -> begin
      match find_id_opt v env with
      | Some (_, v', _) ->
        Var (unlift_id v')
      | None -> failwith @@ "(assign_serial_to_vars, go) unbounded variable (" ^ v.name ^ ")"
    end 
  and go_arith env (psi : Arith.t) : Arith.t = match psi with
    | Int i -> Int i
    | Var v -> begin
      match find_id_opt v env with
      | Some (_, v', _) -> begin
        assert (v'.ty = TyInt);
        Var ({ v' with ty = `Int})
      end
      | None -> failwith @@ "(assign_serial_to_vars, go_arith) unbounded variable (" ^ v.name ^ ")"
    end
    | Op (op, ariths) -> Op (op, List.map (go_arith env) ariths) in
  go env phi
  
let abbrev_variable_numbers_hes ((entry, rules) : Type.simple_ty Hflz.hes) =
  let env = List.map (fun rule -> (lift_id rule.Hflz.var, lift_id rule.Hflz.var, rule.Hflz.var.name)) rules in
  let entry = abbrev_variable_numbers env entry in
  let rules =
    List.map (fun rule -> {
      rule with
      Hflz.body = abbrev_variable_numbers env rule.Hflz.body}) rules in
  entry, rules
