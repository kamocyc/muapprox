module Hflz = Hflmc2_syntax.Hflz
module Id = Hflmc2_syntax.Id
module Type = Hflmc2_syntax.Type
module Arith = Hflmc2_syntax.Arith

let lift_id id =
  { id with Id.ty = Type.TySigma id.Id.ty}

let unlift_id id =
  { id with Id.ty = Type.unsafe_unlift id.Id.ty}

module Env = struct
  type 'a env_element = {
    new_id: 'a Id.t;
    old_id: 'a Id.t;
    number: int;
    basename: string;
  }
  
  type 'a t = 'a env_element list
  
  let init : 'a t = []
  
  let extract_name name =
    let reg = Str.regexp "\\([A-Za-z_'#0-9]*[A-Za-z'#]\\)_*\\d*" in
    ignore @@ Str.search_forward reg name 0;
    let name = Str.matched_group 1 name in
    (* print_endline @@ "name=" ^ name; *)
    name

  let find_by_basename env basename =
    (* find_opt returns the first elements that satysfies a condition, therefore, returns the last element added, which has the largest number  *)
    List.find_opt (fun {basename = basename'; _} -> basename = basename') env
  
  (* add name to environment *)
  let add_arg env old_id =
    let basename = extract_name old_id.Id.name in
    match find_by_basename env basename with
    | Some {number; _} ->
      (* there exists the same name *)
      let next_name = basename ^ string_of_int (number + 1) in
      let new_id = { old_id with name = next_name } in
      new_id, {new_id; old_id; number = number + 1; basename}::env
    | None ->
      let new_id = { old_id with name = basename } in
      new_id, {new_id; old_id; number = 1; basename}::env
  
  let add env old_id =
    let new_id, env = add_arg env (lift_id old_id) in
    (unlift_id new_id, env)
    
  let lookup_by_old_id env v =
    List.find_opt (fun {old_id; _} -> Id.eq old_id v) env
    |> Option.map (fun {new_id; _} -> new_id)
    
end

let abbrev_variable_numbers (env : 'a Type.arg Env.t) (phi : 'a Hflz.t) =
  let rec go (env : 'a Type.arg Env.t) (phi : 'a Hflz.t): 'a Hflz.t =
    match phi with
    | Var v -> begin
      match Env.lookup_by_old_id env v with
      | Some new_id -> Var (unlift_id new_id)
      | None -> failwith @@ "(abbrev_variable_numbers) unbounded variable: " ^ Id.to_string v
    end
    | Abs (x, p) ->
      let new_id, env = Env.add_arg env x in
      Abs (new_id, go env p)
    | Forall (x, p) ->
      let new_id, env = Env.add_arg env x in
      Forall (new_id, go env p)
    | Exists (x, p) ->
      let new_id, env = Env.add_arg env x in
      Exists (new_id, go env p)
    | Bool b -> Bool b
    | Or (p1, p2) -> Or (go env p1, go env p2)
    | And (p1, p2) -> And (go env p1, go env p2)
    | App (p1, p2) -> App (go env p1, go env p2)
    | Arith a -> Arith (go_arith env a)
    | Pred (p, a) -> Pred (p, List.map (go_arith env) a)
  and go_arith (env : 'a Type.arg Env.t) (a : Arith.t) : Arith.t =
    match a with
    | Int i -> Int i
    | Var v -> begin
      match Env.lookup_by_old_id env v with
      | Some new_id -> begin
        match new_id.ty with
        | TyInt -> Var { new_id with ty = `Int }
        | TySigma _ -> failwith "go_arith"
      end
      | None -> failwith @@ "(abbrev_variable_numbers) unbounded variable: " ^ v.name
    end
    | Op (op, a) -> Op (op, List.map (go_arith env) a)
  in
  go env phi
    
  
let abbrev_variable_numbers_hes ((entry, rules) : Type.simple_ty Hflz.hes) =
  let env = Env.init in
  let rules, env =
    List.fold_left
      (fun (rules, env) rule ->
        let var, env = Env.add env rule.Hflz.var in
        ({rule with var}::rules, env)
      )
      ([], env)
      rules in
  let rules = List.rev rules in
  let entry = abbrev_variable_numbers env entry in
  let rules =
    List.map
      (fun rule ->
        let body = abbrev_variable_numbers env rule.Hflz.body in
        {rule with body}
      ) rules in
  Manipulate.Hflz_typecheck.type_check (entry, rules);
  entry, rules

(* 
/*
> dune exec bin2/abbrev.exe -- input.in
*/

/* test */
%HES
S1 =u S_23 10.

S_23 x =u S_24 (x + 1).

S__43 s =u (\s_24. (\a13. (∃a23. a13 = a23)) 10 /\ (∀s123. s123 > 0 \/ ∃s9. s9 = s123) /\ S_A__24 (s + 1 + s_24 + s)) (2 * s) /\ (\s. s = 5) s.

S_24 x =u S__43 (x + 1) /\ S_24 x.

A x =u A__ 10.

S_A__24 x =u S_A___26 (x + 1).

S_A___26 x =u A (x + 1) /\ S_24 x.

A__ x =u x = 10.

/* result */
%HES
Sentry =v S 10.
S x =u S3 (x + 1).
S2 s =u
  (\s2. 
    (\a. ∃a2. a = a2) 10 /\ (∀s3. s3 > 0 \/ (∃s4. s4 = s3))
    /\ S_A (s + 1 + s2 + s))
   (2 * s)
  /\ (\s2. s2 = 5) s.
S3 x =u S2 (x + 1) /\ S3 x.
A x =u A2 10.
S_A x =u S_A2 (x + 1).
S_A2 x =u A (x + 1) /\ S3 x.
A2 x =u x = 10.

 *)