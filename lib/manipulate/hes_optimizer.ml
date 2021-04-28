open Hflmc2_syntax
(* 
module Hesutil = struct
  let iter_app (f : Hflz.t -> unit) phi = 
    match phi with
    | 
end *)

let get_pvar_called_counts hes =
  let preds, graph = Hflz_util.get_dependency_graph hes in
  let graph = Mygraph.reverse_edges graph in
  preds
  |> List.map (fun (i, _var) -> List.length @@ Mygraph.get_next_nids i graph)  

(*
  inline expansion

  if a predicate P1 is called from only one predicate P2
  and depth(P1) > depth(P2)
  then P1 is eliminated by inline expansion
  (the reason of this is trivial when you think the hes as a plain HFLz formula)
*)
module InlineExpansion (* : sig
  val optimize: 'a Hflz.hes -> 'a Hflz.hes
end*) = struct
(* 
  (* 変数の出現を置換 *)
  let replace_var_occurences
      (subst : 'ty Id.t -> 'ty Hflz.t option)
      (hfl : 'ty Hflz.t): 'ty Hflz.t =
    (* TODO: IDのeqが正しく判定される？ *)
    let rec go : 'ty Hflz.t -> 'ty Hflz.t = function
      | Var   id -> begin
        match subst (id) with
        | None -> Var id
        | Some term -> Trans.Subst.Hflz.rename_binding_if_necessary b_env term
      end
      | Bool   b -> Bool b
      | Or (f1, f2) -> Or (go f1, go f2)
      | And (f1, f2) -> And (go f1, go f2)
      | Abs (v, f1) -> Abs (v, go f1)
      | Forall (v, f1) -> Forall (v, go f1)
      | Exists (v, f1) -> Exists (v, go f1)
      | App (f1, f2) -> App (go f1, go f2)
      | Arith t -> Arith t
      | Pred (p, t) -> Pred (p, t)
    in
    (* predicateはboolean以外を返すことは無い。arithmeticの中にhfl predicateは現れない *)
    go hfl *)
    
  let optimize (org_hes : 'a Hflz.hes) =
    let hes_list = (Hflz.merge_entry_rule org_hes) in
    let n = List.length hes_list in
    let pvar_to_id = List.mapi (fun i {Hflz.var;_} -> (var, i)) hes_list in
    let called_counts = get_pvar_called_counts hes_list in
    let expanded = Array.make n false in
    let hes = Array.of_list hes_list in
    List.rev hes_list
    |> List.iteri
      (fun i ({Hflz.body;_ } as rule) ->
        let func_id = n - i - 1 in
        let subst_env =
          pvar_to_id
          |> List.filter_map (fun (v', func_id') ->
            if List.nth called_counts func_id' = 1 && func_id' > func_id then
              Some (v', hes.(func_id').body)
            else None
          )
          |> IdMap.of_list
          in
        let body =
          Trans.Subst.Hflz.hflz ~callback:(fun v _ ->
            match List.find_opt (fun (v', _) -> Id.eq v v') pvar_to_id with
            | Some (_, func_id') -> 
              expanded.(func_id') <- true
            | None -> assert false
          )
          subst_env
          body in
        hes.(func_id) <- { rule with body = Trans.Simplify.hflz body }
      );
    Array.to_list hes
    |> List.mapi (fun i r -> (i, r))
    |> List.filter (fun (id, _) -> not expanded.(id))
    |> List.map (fun (_, r) -> r)
    |> Hflz.decompose_entry_rule
end

let simple_partial_evaluate_hfl phi =
  let rec go phi = match phi with
    | Hflz.Arith a -> Hflz.Arith (Arith.simple_partial_evaluate a)
    | Pred (p, xs) -> Pred (p, List.map Arith.simple_partial_evaluate xs)
    | Var _ | Bool _ -> phi
    | Or (p1, p2) -> Or (go p1, go p2)
    | And(p1, p2) -> And(go p1, go p2)
    | Abs(x, p) -> Abs(x, go p)
    | Forall(x, p) -> Forall(x, go p)
    | Exists(x, p) -> Exists(x, go p)
    | App(p1, p2) -> App(go p1, go p2)
  in
  go phi

let simple_partial_evaluate_hes hes =
  Hflz.merge_entry_rule hes |>
  List.map (fun rule -> { rule with Hflz.body = simple_partial_evaluate_hfl rule.Hflz.body }) |>
  Hflz.decompose_entry_rule

let evaluate_trivial_boolean phi =
  let rec go phi = match phi with
    | Hflz.Pred (p, xs) -> begin
      match Formula.simplify_pred p xs with
      | Some b -> Hflz.Bool b
      | None -> phi
    end
    | And (p1, p2) -> begin
      match go p1, go p2 with
      | Bool true , Bool true -> Bool true
      | Bool false, _ -> Bool false
      | _, Bool false -> Bool false
      | Bool true, p -> p
      | p, Bool true -> p
      | p1, p2 -> And (p1, p2)
    end
    | Or (p1, p2) -> begin
      match go p1, go p2 with
      | Bool false, Bool false -> Bool false
      | Bool true , _ -> Bool true
      | _ , Bool true -> Bool true
      | Bool false , p -> p
      | p , Bool false -> p
      | p1, p2 -> Or (p1, p2)
    end
    | Forall (x, p) -> Forall (x, go p)
    | Exists (x, p) -> Exists(x, go p)
    | Abs (x, p) -> Abs( x, go p)
    | App (p1, p2) -> App (go p1, go p2)
    | Arith _ -> phi
    | Bool _ -> phi
    | Var _ -> phi in
  go phi

let evaluate_trivial_boolean hes =
  Hflz.merge_entry_rule hes |>
  List.map (fun rule -> { rule with Hflz.body = evaluate_trivial_boolean rule.Hflz.body }) |>
  Hflz.decompose_entry_rule
  
let beta_hes (entry, rules) =
  Hflz_util.beta entry,
  List.map (fun rule -> { rule with Hflz.body = Hflz_util.beta rule.Hflz.body }) rules
  
let simplify (hes : Type.simple_ty Hflz.hes)=
  let hes = InlineExpansion.optimize hes in
  let hes = beta_hes hes in
  let hes = simple_partial_evaluate_hes hes in
  let hes = evaluate_trivial_boolean hes in
  (* let hes = Trans.Simplify.hflz_hes hes false in *)
  hes
  
(* 2つ、1つで下、1つで上、1つで中、betaされる *)
(* 1つの述語の中で2回参照される *)
let%expect_test "InlineExpansition.optimize" =
  let open Type in
  let open Hflz in
  let ty2 = TyArrow (id_n 202 TyInt, TyBool ()) in
  let pvars = [
      id_n 000 (TyArrow (id_n 001 (TyInt), TyBool ()));
    id_n 100 (TyArrow (id_n 101 TyInt, TyBool ()));
    id_n 200 (TyArrow (id_n 201 (TySigma ty2), TyBool ()));
    id_n 300 (TyArrow (id_n 301 TyInt, TyBool ()));
    id_n 400 (TyArrow (id_n 401 TyInt, TyBool ()));
    (* id_n 500 (TyArrow (id_n 501 (TySigma (TyBool ())), TyBool ()));
    id_n 600 (TyArrow (id_n 601 (TySigma (TyBool ())), TyBool ())); *)
  ] in
  let nth n = List.nth pvars n in
  (* 
    X1 = \(x101:int). X2 X1 \/ X2 X1;
    X2 = \(x201:int->bool). x201 2 /\ (X4 3);
    X3 = \(x301:int). X4 x301;
    X4 = \(x401:int). x401 = 5 /\ X3 6;
    
    X1 ... x (同じ階層から参照),
    X2 ... o (同じ述語から2回参照), 
    X3 ... x (下から上に参照),
    X4 ... x (2回参照), 
    
    expected result
    X1 = \(x101:int). (\(x201:int->bool). x201 2 /\ (X4 3)) X1 \/ (\(x201:int->bool). x201 2 /\ (X4 3)) X1;
    X3 = \(x301:int). X4 x301;
    X4 = \(x401:int). x401 = 5 /\ X3 6;
    
    
    X1 = \(x101:int). (X1 2 /\ X4 3) \/ (X1 2 /\ X4 3);
    X3 = \(x301:int). X4 x301;
    X4 = \(x401:int). x401 = 5 /\ X3 6;
    
   *)
  let org = [
    {
      fix = Fixpoint.Greatest;
      var = nth 1;
      body = Abs (id_n 101 TyInt, Or (App (Var (nth 2), Var (nth 1)), App (Var (nth 2), Var (nth 1))));
    };{
      fix = Fixpoint.Greatest;
      var = nth 2;
      body = Abs (id_n 201 (TySigma ty2), And (App (Var (id_n 201 ty2), Arith (Int 2)), App (Var (nth 4), Arith (Int 3))));
    };{
      fix = Fixpoint.Greatest;
      var = nth 3;
      body = Abs (id_n 301 TyInt, App (Var (nth 4), Arith (Var (id_n 301 `Int))))
    };{
      fix = Fixpoint.Greatest;
      var = nth 4;
      body = Abs (id_n 401 TyInt, And (Pred (Eq, [Var (id_n 401 `Int); Int 5]), App (Var (nth 3), Arith (Int 6))))
    }] in
  Hflz_typecheck.type_check (Bool true, org);
  ignore [%expect.output];
  print_endline "OK";
  [%expect {| OK |}];
  print_endline @@ Print_syntax.show_hes org;
  [%expect {|
    {fix: Fixpoint.Greatest
    var: { Id.name = "x_100"; id = 100;
      ty =
      (Type.TyArrow ({ Id.name = "x_101"; id = 101; ty = Type.TyInt },
         (Type.TyBool ())))
      }
    body: λx_101101:int.x_200200 x_100100 || x_200200 x_100100}
    {fix: Fixpoint.Greatest
    var: { Id.name = "x_200"; id = 200;
      ty =
      (Type.TyArrow (
         { Id.name = "x_201"; id = 201;
           ty =
           (Type.TySigma
              (Type.TyArrow ({ Id.name = "x_202"; id = 202; ty = Type.TyInt },
                 (Type.TyBool ()))))
           },
         (Type.TyBool ())))
      }
    body: λx_201201:(int -> bool).x_201201 2 && x_400400 3}
    {fix: Fixpoint.Greatest
    var: { Id.name = "x_300"; id = 300;
      ty =
      (Type.TyArrow ({ Id.name = "x_301"; id = 301; ty = Type.TyInt },
         (Type.TyBool ())))
      }
    body: λx_301301:int.x_400400 x_301301}
    {fix: Fixpoint.Greatest
    var: { Id.name = "x_400"; id = 400;
      ty =
      (Type.TyArrow ({ Id.name = "x_401"; id = 401; ty = Type.TyInt },
         (Type.TyBool ())))
      }
    body: λx_401401:int.x_401401 = 5 && x_300300 6} |}];
  let hes = InlineExpansion.optimize (Bool true, org) in
  ignore [%expect.output];
  (* ignore [%expect.output]; *)
  Hflz_typecheck.type_check (Bool true, org);
  ignore [%expect.output];
  print_endline "OK";
  [%expect {| OK |}];
  print_endline @@ Print_syntax.show_hes (snd hes);
  (* print_endline @@ show_hes hes; *)
  (* print_endline @@ Util.fmt_string (Print_syntax.hflz_hes_rule Print_syntax.simple_ty_) rule; *)
  [%expect {|
    {fix: Fixpoint.Greatest
    var: { Id.name = "x_100"; id = 100;
      ty =
      (Type.TyArrow ({ Id.name = "x_101"; id = 101; ty = Type.TyInt },
         (Type.TyBool ())))
      }
    body: λx_101101:int.x_100100 2 && x_400400 3 || x_100100 2 && x_400400 3}
    {fix: Fixpoint.Greatest
    var: { Id.name = "x_300"; id = 300;
      ty =
      (Type.TyArrow ({ Id.name = "x_301"; id = 301; ty = Type.TyInt },
         (Type.TyBool ())))
      }
    body: λx_301301:int.x_400400 x_301301}
    {fix: Fixpoint.Greatest
    var: { Id.name = "x_400"; id = 400;
      ty =
      (Type.TyArrow ({ Id.name = "x_401"; id = 401; ty = Type.TyInt },
         (Type.TyBool ())))
      }
    body: λx_401401:int.x_401401 = 5 && x_300300 6} |}]

let eliminate_unreachable_predicates (hes : 'a Hflz.hes) : 'a Hflz.hes =
  let rules = Hflz.merge_entry_rule hes in
  let _, rgraph = Hflz_util.get_dependency_graph rules in
  let reachables = Mygraph.reachable_nodes_from ~start_is_reachable_initially:true 0 rgraph in
  let rules = 
    List.mapi (fun i r -> r, (List.find_all ((=)i) reachables <> [])) rules
    |> List.filter_map (fun (r, b) -> if b then Some r else None) in
  Hflz.decompose_entry_rule rules
