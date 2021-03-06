
open Hflz_typecheck
open Hflz
open Hflz_manipulate
module Util = Hflmc2_util

let%expect_test "desugar_formula" =
  let open Type in
  let sugar : simple_ty Hflz.Sugar.t =
    (* true && (not (true && ∀x2. 1 >= x2 || ∃x3. not (true && x4 5))) *)
    (* => *)
    (* true && (false || ∃x2. 1 < x2 && ∀x3. true && x4 5) *)
    And (Bool true, Not (And (Bool true, Forall (id_n 2 TyInt, Or (Pred (Ge, [Int 1; Var (id_n 2 `Int)]), Exists (id_n 3 TyInt, Not (And (Bool true, App (Var (id_n 4 (TyBool ())), Arith (Int 5)))))))))) in
  let desugar = Hflz.desugar_formula sugar in
  ignore [%expect.output];
  print_endline @@ show_hflz desugar;
  [%expect {| true && (false || (∃x_22.1 < x_22 && (∀x_33.true && x_44 5))) |}]


let%expect_test "to_args" =
  let open Type in
  let res = to_args @@ TyArrow (id_n 1 TyInt, TyArrow (id_n 2 TyInt, TyArrow (id_n 3 (TySigma (TyBool ())), TyBool ()))) in
  ignore [%expect.output];
  Util.print_list (Id.show (fun fmt ty_ -> pp_simple_argty fmt ty_)) res;
  [%expect {|
    [ { Id.name = "x_3"; id = 3; ty = (Type.TySigma (Type.TyBool ())) };
    { Id.name = "x_2"; id = 2; ty = Type.TyInt };
    { Id.name = "x_1"; id = 1; ty = Type.TyInt } ] |}]


let%expect_test "to_abs" =
  let open Type in
  let res = to_abs [
    { Id.name = "x_3"; id = 3; ty = (Type.TySigma (Type.TyBool ())) };
    { Id.name = "x_2"; id = 2; ty = Type.TyInt };
    { Id.name = "x_1"; id = 1; ty = Type.TyInt } ] (Bool true) in
  ignore [%expect.output];
  print_endline @@ show_hflz_full res;
  [%expect {|
    (Hflz.Abs ({ Id.name = "x_3"; id = 4; ty = (Type.TySigma (Type.TyBool ())) },
       (Hflz.Abs ({ Id.name = "x_2"; id = 5; ty = Type.TyInt },
          (Hflz.Abs ({ Id.name = "x_1"; id = 6; ty = Type.TyInt },
             (Hflz.Bool true)))
          ))
       )) |}]


let%expect_test "to_abs'" =
  let open Type in
  let res = to_abs' [
    { Id.name = "x_3"; id = 3; ty = (Type.TySigma (Type.TyBool ())) };
    { Id.name = "x_2"; id = 2; ty = Type.TyInt };
    { Id.name = "x_1"; id = 1; ty = Type.TyInt } ] (Bool true) in
  ignore [%expect.output];
  print_endline @@ show_hflz_full res;
  [%expect {|
    (Hflz.Abs ({ Id.name = "x_3"; id = 3; ty = (Type.TySigma (Type.TyBool ())) },
       (Hflz.Abs ({ Id.name = "x_2"; id = 2; ty = Type.TyInt },
          (Hflz.Abs ({ Id.name = "x_1"; id = 1; ty = Type.TyInt },
             (Hflz.Bool true)))
          ))
       )) |}]
    
let%expect_test "to_forall" =
  let res = to_forall [
    { Id.name = "x_3"; id = 3; ty = (Type.TySigma (Type.TyBool ())) };
    { Id.name = "x_2"; id = 2; ty = Type.TyInt };
    { Id.name = "x_1"; id = 1; ty = Type.TyInt } ] (Bool true) in
  ignore [%expect.output];
  print_endline @@ show_hflz_full res;
  [%expect {|
    (Hflz.Forall (
       { Id.name = "x_3"; id = 3; ty = (Type.TySigma (Type.TyBool ())) },
       (Hflz.Forall ({ Id.name = "x_2"; id = 2; ty = Type.TyInt },
          (Hflz.Forall ({ Id.name = "x_1"; id = 1; ty = Type.TyInt },
             (Hflz.Bool true)))
          ))
       )) |}]

let%expect_test "to_vars" =
  let open Type in
  let res =
    to_vars
      (Hflz.Abs ({ Id.name = "x_3"; id = 3; ty = (Type.TySigma (Type.TyBool ())) },
       (Hflz.Abs ({ Id.name = "x_2"; id = 2; ty = Type.TyInt },
          (Hflz.Abs ({ Id.name = "x_1"; id = 1; ty = Type.TyInt },
             (Hflz.Bool true)))
          ))
       )) (Bool false) in
  ignore [%expect.output];
  print_endline @@ show_hflz_full res;
  [%expect {|
    (Hflz.App (
       (Hflz.App (
          (Hflz.App ((Hflz.Bool false),
             (Hflz.Arith (Arith.Var { Id.name = "x_1"; id = 1; ty = `Int })))),
          (Hflz.Arith (Arith.Var { Id.name = "x_2"; id = 2; ty = `Int })))),
       (Hflz.Var { Id.name = "x_3"; id = 3; ty = (Type.TyBool ()) }))) |}] 

let%expect_test "to_app" =
  let open Type in
  let seed = [1; 2; 3] in
  let res =
    to_app
      (Bool false)
      (List.map (fun i -> Arith(Var (id_n i `Int))) seed) in
  ignore [%expect.output];
  print_endline @@ show_hflz_full res;
  [%expect {|
    (Hflz.App (
       (Hflz.App (
          (Hflz.App ((Hflz.Bool false),
             (Hflz.Arith (Arith.Var { Id.name = "x_1"; id = 1; ty = `Int })))),
          (Hflz.Arith (Arith.Var { Id.name = "x_2"; id = 2; ty = `Int })))),
       (Hflz.Arith (Arith.Var { Id.name = "x_3"; id = 3; ty = `Int })))) |}] 

let%expect_test "make_guessed_terms" =
  let res = make_guessed_terms 2 10 [id_n 1 `Int; id_n 2 `Int] in
  ignore [%expect.output];
  Util.print_list (fun r -> show_hflz (Arith r)) res;
  [%expect {|
    [ 2 * x_11 + 10;
    (-2) * x_11 + 10;
    2 * x_22 + 10;
    (-2) * x_22 + 10 ] |}];
  let res = make_guessed_terms 2 10 [] in
  ignore [%expect.output];
  Util.print_list (fun r -> show_hflz (Arith r)) res;
  [%expect {|[ 10 ]|}]

let%expect_test "make_guessed_terms_simple" =
  let res = make_guessed_terms_simple 2 10 [id_n 1 `Int; id_n 2 `Int] in
  ignore [%expect.output];
  Util.print_list (fun r -> show_hflz (Arith r)) res;
  [%expect {|
    [ 10;
    2 * x_11;
    2 * x_22;
    (-2) * x_11;
    (-2) * x_22 ] |}];
  let res = make_guessed_terms_simple 2 10 [] in
  ignore [%expect.output];
  Util.print_list (fun r -> show_hflz (Arith r)) res;
  [%expect {|[ 10 ]|}]
  
let%expect_test "rev_abs" =
  let res =
    rev_abs
      (Hflz.Abs ({ Id.name = "x_3"; id = 3; ty = (Type.TySigma (Type.TyBool ())) },
        (Hflz.Abs ({ Id.name = "x_2"; id = 2; ty = Type.TyInt },
          (Hflz.Abs ({ Id.name = "x_1"; id = 1; ty = Type.TyInt },
              (Hflz.Bool true)))
          ))
        )) in
  print_endline @@ show_hflz_full res;
  [%expect {|
    (Hflz.Abs ({ Id.name = "x_1"; id = 1; ty = Type.TyInt },
       (Hflz.Abs ({ Id.name = "x_2"; id = 2; ty = Type.TyInt },
          (Hflz.Abs (
             { Id.name = "x_3"; id = 3; ty = (Type.TySigma (Type.TyBool ())) },
             (Hflz.Bool true)))
          ))
       )) |}]


let%expect_test "extract_abstraction" =
  let open Type in
  let open Arith in
  let (f, rule) =
    extract_abstraction
      (Abs (id_n 1 (TyInt), Abs (id_n 2 (TySigma (TyBool ())),
        App (Var (id_n 4 (TyArrow (id_n 5 TyInt, TyBool ()))), Arith (Op (Add, [Var (id_n 1 `Int); Op (Mult, [Var (id_n 2 `Int); Var (id_n 3 `Int)])])))
      )))
      [(id_n 4 (TyArrow (id_n 5 TyInt, TyBool ())))]
      "a" in
  ignore [%expect.output];
  print_endline @@ show_hflz f;
  print_endline @@ Util.fmt_string (Print_syntax.hflz_hes_rule Print_syntax.simple_ty_) rule;
  [%expect {|
    a_sub78 x_33
    a_sub78 =ν λx_33:int.λx_11:int.λx_22:bool.x_44 (x_11 + x_22 * x_33) |}]


let%expect_test "in_forall" =
  let open Type in
  let open Arith in
  let v =
    in_forall
      (Forall (id_n 3 TyInt, Forall (id_n 4 (TySigma (TyBool ())), Abs (id_n 1 (TyInt), Abs (id_n 2 (TySigma (TyBool ())), Bool true))))) in
  ignore [%expect.output];
  print_endline @@ show_hflz_full v;
  [%expect {|
    (Hflz.Abs ({ Id.name = "x_1"; id = 1; ty = Type.TyInt },
       (Hflz.Abs (
          { Id.name = "x_2"; id = 2; ty = (Type.TySigma (Type.TyBool ())) },
          (Hflz.Forall ({ Id.name = "x_3"; id = 3; ty = Type.TyInt },
             (Hflz.Forall (
                { Id.name = "x_4"; id = 4; ty = (Type.TySigma (Type.TyBool ())) },
                (Hflz.Bool true)))
             ))
          ))
       )) |}]


let%expect_test "encode_body_exists_formula_sub" =
  let open Type in
  let p = id_n 10 (TySigma (TyArrow (id_n 12 TyInt, (TyArrow (id_n 11 TyInt, TyBool ()))))) in
  (* 高階変数の扱い *)
  (* その時点で使える自由変数ということは、直前のラムダ抽象も含まれる？ => いや、そこは使わない。あくまで式の中の型を取得するだけなので、別。free var のみを使用 *)
  (* ∃x_100.∃x_300.λx_1:int.λx_2:(int -> bool).(x_10 :int -> int -> bool) (x_1 + x_3) x_300 && (x_2:int -> bool) x_5 && (x_4:int -> bool) x_100 *)
  (* other predicates = x10 : int -> bool *)
  (* arguments in the term's type = x1 : int, x2 : int -> bool *)
  (* free variables = x3 : int, x4 : int -> bool, x5 : int *)
  let org_formula =
    Exists (id_n 100 TyInt, Exists (id_n 300 TyInt, Abs (id_n 1 TyInt, Abs (id_n 2 (TySigma (TyArrow (id_n 31 TyInt, TyBool ()))),
      And (
        App (App (Var { p with ty = unsafe_unlift p.ty }, 
          Arith (Op (Add, [Var (id_n 1 `Int); Var (id_n 3 `Int)]))), Arith (Var (id_n 300 `Int))),
        And (App (Var (id_n 2 (TyArrow (id_n 31 TyInt, TyBool ()))), Arith (Var (id_n 5 `Int))),
          App (Var (id_n 4 (TyArrow (id_n 32 TyInt, TyBool ()))), Arith (Var (id_n 100 `Int)))))
      )))) in
  print_endline @@ "original: " ^ show_hflz org_formula;
  [%expect {|
    original: ∃x_100100.
     ∃x_300300.
      λx_11:int.
       λx_22:(int -> bool).
        x_1010 (x_11 + x_33) x_300300 && x_22 x_55 && x_44 x_100100 |}];
  let (replaced, rules) =
    encode_body_exists_formula_sub
      None
      1
      10
      [p]
      org_formula
    in
  ignore [%expect.output];
  print_endline @@ string_of_int @@ List.length rules;
  let rule = List.nth rules 0 in
  print_endline @@ "replaced: " ^ show_hflz replaced;
  [%expect {|
    1
    replaced: λx_11:int.
     λx_22:(int -> bool).
      ∀x_100100.
       ∀x_300300.
        x_300300 < 10 || x_300300 < 1 * x_33 || x_300300 < 1 * x_55
        || x_300300 < (-1) * x_33
        || x_300300 < (-1) * x_55
        || x_100100 < 10 || x_100100 < 1 * x_33 || x_100100 < 1 * x_55
           || x_100100 < (-1) * x_33
           || x_100100 < (-1) * x_55
        || Exists9 x_33 x_44 x_55 x_11 x_22 x_100100 x_300300 |}];
  print_endline @@ "fix: " ^ Fixpoint.show rule.fix;
  print_endline @@ "var: " ^ Id.show pp_simple_ty rule.var;
  print_endline @@ "rule: " ^ show_hflz rule.body;
  [%expect {|
    fix: Fixpoint.Greatest
    var: { Id.name = "Exists9"; id = 9;
      ty =
      (Type.TyArrow ({ Id.name = "x_3"; id = 3; ty = Type.TyInt },
         (Type.TyArrow (
            { Id.name = "x_4"; id = 4;
              ty =
              (Type.TySigma
                 (Type.TyArrow ({ Id.name = "x_32"; id = 32; ty = Type.TyInt },
                    (Type.TyBool ()))))
              },
            (Type.TyArrow ({ Id.name = "x_5"; id = 5; ty = Type.TyInt },
               (Type.TyArrow ({ Id.name = "x_1"; id = 1; ty = Type.TyInt },
                  (Type.TyArrow (
                     { Id.name = "x_2"; id = 2;
                       ty =
                       (Type.TySigma
                          (Type.TyArrow (
                             { Id.name = "x_31"; id = 31; ty = Type.TyInt },
                             (Type.TyBool ()))))
                       },
                     (Type.TyArrow (
                        { Id.name = "x_100"; id = 100; ty = Type.TyInt },
                        (Type.TyArrow (
                           { Id.name = "x_300"; id = 300; ty = Type.TyInt },
                           (Type.TyBool ())))
                        ))
                     ))
                  ))
               ))
            ))
         ))
      }
    rule: λx_33:int.
     λx_44:(int -> bool).
      λx_55:int.
       λx_11:int.
        λx_22:(int -> bool).
         λx_100100:int.
          λx_300300:int.
           ((λx_11:int.
              λx_22:(int -> bool).
               x_1010 (x_11 + x_33) x_300300 && x_22 x_55 && x_44 x_100100)
             x_11 x_22
            || (λx_11:int.
                 λx_22:(int -> bool).
                  x_1010 (x_11 + x_33) (-x_300300) && x_22 x_55 && x_44 x_100100)
                x_11 x_22
            || (λx_11:int.
                 λx_22:(int -> bool).
                  x_1010 (x_11 + x_33) x_300300 && x_22 x_55 && x_44 (-x_100100))
                x_11 x_22
            || (λx_11:int.
                 λx_22:(int -> bool).
                  x_1010 (x_11 + x_33) (-x_300300)
                  && x_22 x_55 && x_44 (-x_100100))
                x_11 x_22
            || Exists9 x_33 x_44 x_55 x_11 x_22 (x_100100 - 1) x_300300
            || Exists9 x_33 x_44 x_55 x_11 x_22 x_100100 (x_300300 - 1))
           && x_100100 >= 0 && x_300300 >= 0 |}];
  (* check well-typedness *)
  let hes = [
    {
      var = id_n 200 (TyArrow (id_n 3 TyInt, TyArrow (id_n 4 @@ TySigma (TyArrow (id_n 32 TyInt, TyBool ())),
        TyArrow (id_n 5 TyInt, TyArrow (id_n 1 TyInt, (TyArrow (id_n 2 (TySigma (TyArrow (id_n 31 TyInt, TyBool ()))), TyBool ())))))));
      fix = Fixpoint.Greatest;
      body = Abs (id_n 3 TyInt, Abs (id_n 4 (TySigma (TyArrow (id_n 32 TyInt, TyBool ()))), Abs (id_n 5 TyInt, replaced))) };
    {
      var = { p with ty = unsafe_unlift p.ty};
      body = Abs (id_n 12 TyInt, Abs (id_n 11 TyInt, Bool true));
      fix = Fixpoint.Greatest };
    rule ] in
  let hes = decompose_lambdas_hes (Bool true, hes) in
  type_check hes;
  ignore [%expect.output];
  print_endline "OK";
  [%expect {|OK|}]


