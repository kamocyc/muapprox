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
  |> List.map (fun (i, var) -> List.length @@ Mygraph.get_next_nids i graph)  

(*
  inline expansion

  if a predicate P1 is called from only one predicate P2
  and depth(P1) > depth(P2)
  then P1 is eliminated by inline expansion
  (the reason of this is trivial when you think the hes as hflz)
*)
module InlineExpansition : sig
  val optimize: 'a Hflz.hes -> 'a Hflz.hes
end = struct
  let optimize (hes_list : 'a Hflz.hes) =
    let n = List.length hes_list in
    let pvar_to_id = List.mapi (fun i {Hflz.var;_} -> (var, i)) hes_list in
    let called_counts = get_pvar_called_counts hes_list in
    let expanded = Array.make n false in
    let hes = Array.of_list hes_list in
    List.rev hes_list
    |> List.iteri
      (fun i ({Hflz.body;_ } as rule) ->
        let func_id = n - i - 1 in
        let body =
          Hflz_manipulate.replace_var_occurences
          (fun v ->
            match List.find_opt (fun (v', _) -> Id.eq v v') pvar_to_id with
            | Some (_, func_id') -> 
              if List.nth called_counts func_id' = 1 && func_id' > func_id then (
                expanded.(func_id') <- true;
                hes.(func_id').body
              ) else Var v
            | None -> Var v
          )
          body in
        hes.(func_id) <- { rule with body = Trans.Simplify.hflz body }
      );
    Array.to_list hes
    |> List.mapi (fun i r -> (i, r))
    |> List.filter (fun (id, {Hflz.var; _}) -> not expanded.(id))
    |> List.map (fun (_, r) -> r)
end

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
  Hflz_typecheck.type_check org;
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
    body: λx_101101:int.
     (x_200200 :(int -> bool) -> bool) (x_100100 :int -> bool)
     || (x_200200 :(int -> bool) -> bool) (x_100100 :int -> bool)}
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
    body: λx_201201:(int -> bool).
     (x_201201 :int -> bool) 2 && (x_400400 :int -> bool) 3}
    {fix: Fixpoint.Greatest
    var: { Id.name = "x_300"; id = 300;
      ty =
      (Type.TyArrow ({ Id.name = "x_301"; id = 301; ty = Type.TyInt },
         (Type.TyBool ())))
      }
    body: λx_301301:int.(x_400400 :int -> bool) x_301301}
    {fix: Fixpoint.Greatest
    var: { Id.name = "x_400"; id = 400;
      ty =
      (Type.TyArrow ({ Id.name = "x_401"; id = 401; ty = Type.TyInt },
         (Type.TyBool ())))
      }
    body: λx_401401:int.x_401401 = 5 && (x_300300 :int -> bool) 6} |}];
  let hes = InlineExpansition.optimize org in
  ignore [%expect.output];
  (* ignore [%expect.output]; *)
  Hflz_typecheck.type_check org;
  ignore [%expect.output];
  print_endline "OK";
  [%expect {| OK |}];
  print_endline @@ Print_syntax.show_hes hes;
  (* print_endline @@ show_hes hes; *)
  (* print_endline @@ Util.fmt_string (Print_syntax.hflz_hes_rule Print_syntax.simple_ty_) rule; *)
  [%expect {|
    {fix: Fixpoint.Greatest
    var: { Id.name = "x_100"; id = 100;
      ty =
      (Type.TyArrow ({ Id.name = "x_101"; id = 101; ty = Type.TyInt },
         (Type.TyBool ())))
      }
    body: λx_101101:int.
     (x_100100 :int -> bool) 2 && (x_400400 :int -> bool) 3
     || (x_100100 :int -> bool) 2 && (x_400400 :int -> bool) 3}
    {fix: Fixpoint.Greatest
    var: { Id.name = "x_300"; id = 300;
      ty =
      (Type.TyArrow ({ Id.name = "x_301"; id = 301; ty = Type.TyInt },
         (Type.TyBool ())))
      }
    body: λx_301301:int.(x_400400 :int -> bool) x_301301}
    {fix: Fixpoint.Greatest
    var: { Id.name = "x_400"; id = 400;
      ty =
      (Type.TyArrow ({ Id.name = "x_401"; id = 401; ty = Type.TyInt },
         (Type.TyBool ())))
      }
    body: λx_401401:int.x_401401 = 5 && (x_300300 :int -> bool) 6} |}]
