open OUnit
open Ast.Logic
open Testutil
open CEGISprover.Logicutil

(*
let files_in_dir dirname =
  let files = Array.to_list @@ Sys.readdir dirname in
  List.filter files ~f:(fun x -> `Yes = Sys.is_file x)

let load_formulas dir =
  let files = files_in_dir dir in
  List.map files ~f:(fun (filename:string) ->
      match Convert.Parser.from_file (dir ^ filename) with
      | Ok(phi) -> (filename, phi)
      | Error _ -> failwith "unknown filename")

let provable_dir = Sys.getcwd () ^ "/../../../../examples/provable/"
let unprovable_dir = Sys.getcwd () ^ "/../../../../examples/unprovable/"

let mk_dataset () =
  let provables = load_formulas provable_dir in
  let unprovables = load_formulas unprovable_dir in
  (provables, unprovables)

let approx_test () =
  let provables, unprovables = mk_dataset () in
  List.iter provables ~f:(fun (filename, phi) ->
      let state = Locallysolver.solve phi in
      assert_bool filename (Status.Invalid <> state) (* TODO *)
    );
  List.iter unprovables ~f:(fun (filename, phi) ->
      let state = Locallysolver.solve phi in
      assert_bool filename (Status.Valid <> state) (* TODO *)
    )
*)

(* utils *)
let atm_comp_lt t1 t2 = T_int.mk_lt t1 t2 Dummy
let atm_comp_leq t1 t2 = T_int.mk_leq t1 t2 Dummy

let trm_from_fml fml = Term.mk_funapp (T_bool.Formula fml) [] Dummy



(* constant formulas *)
let fml_true = Formula.mk_atom (Atom.mk_true Dummy) Dummy
let fml_false = Formula.mk_atom (Atom.mk_false Dummy) Dummy

(* constant terms *)
let trm_int_1 = T_int.mk_from_int 1 Dummy
let trm_int_4 = T_int.mk_from_int 4 Dummy
let trm_int_5 = T_int.mk_from_int 5 Dummy
let trm_int_6 = T_int.mk_from_int 6 Dummy
let trm_int_10 = T_int.mk_from_int 10 Dummy
let trm_int_minus_4 = T_int.mk_from_int (-4) Dummy
let trm_real_4_5 = T_int.mk_real "4.5" Dummy

(* bool terms *)
let trm_fml_true = trm_from_fml fml_true
let trm_fml_false = trm_from_fml fml_false

(* term calculate *)
(* add *)
let trm_int_1_plus_6 = T_int.mk_add trm_int_1 trm_int_6 Dummy
let trm_int_minue_4_plus_6 = T_int.mk_add trm_int_6 trm_int_minus_4 Dummy
(* sub *)
let trm_int_minue_4_minus_6 = T_int.mk_sub trm_int_minus_4 trm_int_6 Dummy
let trm_int_6_minue_minus_4 = T_int.mk_sub trm_int_6 trm_int_minus_4 Dummy
(* mult *)
let trm_int_6_times_minus_4 = T_int.mk_mult trm_int_6 trm_int_minus_4 Dummy
let trm_int_6_times_10 = T_int.mk_mult trm_int_6 trm_int_10 Dummy
(* div *)
let trm_int_6_div_minus_4 = T_int.mk_div trm_int_6 trm_int_minus_4 Dummy
let trm_int_6_div_10 = T_int.mk_div trm_int_6 trm_int_10 Dummy
(* mod *)
let trm_int_6_mod_4 = T_int.mk_mod trm_int_6 trm_int_4 Dummy
let trm_int_10_mod_6 = T_int.mk_mod trm_int_10 trm_int_6 Dummy
let trm_int_10_mod_5 = T_int.mk_mod trm_int_10 trm_int_5 Dummy

(* if then else *)
let trm_if_t_then_t_else_f = T_bool.mk_if_then_else trm_fml_true trm_fml_true trm_fml_false Dummy
let trm_if_f_then_t_else_f = T_bool.mk_if_then_else trm_fml_true trm_fml_true trm_fml_false Dummy
let trm_if_t_then_f_else_t = T_bool.mk_if_then_else trm_fml_true trm_fml_true trm_fml_false Dummy
let trm_if_f_then_f_else_t = T_bool.mk_if_then_else trm_fml_true trm_fml_true trm_fml_false Dummy
let trm_if_t_then_10_else_minus_4 = T_bool.mk_if_then_else trm_fml_true trm_int_10 trm_int_minus_4 Dummy
let trm_if_f_then_10_else_minus_4 = T_bool.mk_if_then_else trm_fml_false trm_int_10 trm_int_minus_4 Dummy


  (* formula *)
(* compare two integers *)
let fml_1_lt_6 = Formula.mk_atom (atm_comp_lt trm_int_1 trm_int_6) Dummy
let fml_1_lt_minus_4 = Formula.mk_atom (atm_comp_lt trm_int_1 trm_int_minus_4) Dummy
let fml_6_leq_1 = Formula.mk_atom (atm_comp_leq trm_int_6 trm_int_1) Dummy
let fml_1_leq_1 = Formula.mk_atom (atm_comp_leq trm_int_1 trm_int_1) Dummy

(* compare calc of integers *)
let fml_1_plus_6_lt_6_mult_minus_4 = Formula.mk_atom(atm_comp_lt trm_int_1_plus_6 trm_int_6_times_minus_4) Dummy

(* unop, binop *)
let fml_neg_t = Formula.mk_neg fml_true Dummy
let fml_and_t_t = Formula.mk_and fml_true fml_true Dummy
let fml_and_t_f = Formula.mk_and fml_true fml_false Dummy
let fml_or_t_f = Formula.mk_or fml_true fml_false Dummy
let fml_or_f_f = Formula.mk_or fml_false fml_false Dummy

  (* term *)
(* including formula *)
let trm_fml_and_t_t = trm_from_fml fml_and_t_t
let trm_fml_or_f_f = trm_from_fml fml_or_f_f
let trm_true_and_true = trm_from_fml (Formula.BinaryOp (Formula.And, fml_true, fml_true, Dummy))


let eval_formula_test =
  [
    { name = "const true"; actual = (fun () -> eval_formula fml_true); expected = true; };
    { name = "const false"; actual = (fun () -> eval_formula fml_false); expected = false; };

    { name = "1 < 6"; actual = (fun () -> eval_formula fml_1_lt_6); expected = true; };
    { name = "1 < -4"; actual = (fun () -> eval_formula fml_1_lt_minus_4); expected = false; };
    { name = "6 <= 1"; actual = (fun () -> eval_formula fml_6_leq_1); expected = false; };
    { name = "1 <= 1"; actual = (fun () -> eval_formula fml_1_leq_1); expected = true; };
    { name = "1+6 < 6*-4"; actual = (fun () -> eval_formula fml_1_plus_6_lt_6_mult_minus_4); expected = false; };

    { name = "neg t = f"; actual = (fun () -> eval_formula fml_neg_t); expected = false; };
    { name = "t/\\t = t"; actual = (fun () -> eval_formula fml_and_t_t); expected = true; };
    { name = "t/\\f = f"; actual = (fun () -> eval_formula fml_and_t_f); expected = false; };
    { name = "t\\/f = t"; actual = (fun () -> eval_formula fml_or_t_f); expected = true; };
    { name = "f\\/f = f"; actual = (fun () -> eval_formula fml_or_f_f); expected = false; };
  ]

let eval_term_test =
  [
    (* number *)
    { name = "const 1"; actual = (fun () -> eval_term trm_int_1); expected = IntLit (Bigint.of_int 1) };
    { name = "const 4.5"; actual = (fun () -> eval_term trm_real_4_5); expected = RealLit 4.5 };
    (* int calc *)
    { name = "1+6 = 7"; actual = (fun () -> eval_term trm_int_1_plus_6); expected = IntLit (Bigint.of_int 7) };
    { name = "-4+6 = 2"; actual = (fun () -> eval_term trm_int_minue_4_plus_6); expected = IntLit (Bigint.of_int 2) };
    { name = "-4-6 = -10"; actual = (fun () -> eval_term trm_int_minue_4_minus_6); expected = IntLit (Bigint.of_int (-10)) };
    { name = "6-(-4) = 10"; actual = (fun () -> eval_term trm_int_6_minue_minus_4); expected = IntLit (Bigint.of_int 10) };
    { name = "6*-4 = -24"; actual = (fun () -> eval_term trm_int_6_times_minus_4); expected = IntLit (Bigint.of_int (-24)) };
    { name = "6*10 = 60"; actual = (fun () -> eval_term trm_int_6_times_10); expected = IntLit (Bigint.of_int 60) };
    { name = "6/(-4) = -1"; actual = (fun () -> eval_term trm_int_6_div_minus_4); expected = IntLit (Bigint.of_int (-1)) };
    { name = "6/10 = 0"; actual = (fun () -> eval_term trm_int_6_div_10); expected = IntLit (Bigint.of_int 0) };
    { name = "6%4 = 2"; actual = (fun () -> eval_term trm_int_6_mod_4); expected = IntLit (Bigint.of_int 2) };

    (* bool *)
    { name = "just true"; actual = (fun () -> eval_term trm_fml_true); expected = BoolLit true };
    { name = "just false"; actual = (fun () -> eval_term trm_fml_false); expected = BoolLit false };
    (* if then else *)
    { name = "if T then T else F"; actual = (fun () -> eval_term trm_if_t_then_t_else_f); expected = BoolLit true };
    { name = "if F then T else F"; actual = (fun () -> eval_term trm_if_f_then_t_else_f); expected = BoolLit true };
    { name = "if T then F else T"; actual = (fun () -> eval_term trm_if_t_then_f_else_t); expected = BoolLit true };
    { name = "if F then F else T"; actual = (fun () -> eval_term trm_if_f_then_f_else_t); expected = BoolLit true };
    { name = "if T then 10 else -4"; actual = (fun () -> eval_term trm_if_t_then_10_else_minus_4); 
      expected = IntLit (Bigint.of_int 10) };
    { name = "if F then 10 else -4"; actual = (fun () -> eval_term trm_if_f_then_10_else_minus_4);
      expected = IntLit (Bigint.of_int (-4)) };
  ]

(* test for constraint extraction *)
let constraint_extraction_test =
  let open CEGISprover in
  let open Ast in
  let tx, ty = Term.mk_var (Ident.Tvar "x") (T_int.SInt) Dummy, Term.mk_var (Ident.Tvar "y") (T_int.SInt) Dummy in
  let tn = Term.mk_var (Ident.Tvar "n") (T_int.SInt) Dummy in
  let px, py = Predicate.mk_var (Ident.Pvar "X") [T_int.SInt], Predicate.mk_var (Ident.Pvar "Y") [T_int.SInt] in
  (* muY(y).y=0 \/ Y(y-1) *)
  let nat = Predicate.mk_fix (Predicate.Mu) (Ident.Pvar "Y") [(Ident.Tvar "y", T_int.SInt)]
              (Formula.mk_or (Formula.mk_atom (T_bool.mk_eq ty (T_int.zero Dummy) Dummy) Dummy)
                 (Formula.mk_atom (Atom.mk_app py [ty] Dummy) Dummy) Dummy) in
  (* nuX(x).X(x+1) /\ nat(x) *)
  let nat' = Predicate.mk_fix (Predicate.Nu) (Ident.Pvar "X") [(Ident.Tvar "x", T_int.SInt)]
               (Formula.mk_and (Formula.mk_atom (Atom.mk_app px [T_int.mk_add (tx) (T_int.one Dummy) Dummy] Dummy) Dummy)
                  (Formula.mk_atom (Atom.mk_app nat [tx] Dummy) Dummy) Dummy) in
  (* nuX(x).X(x+1) /\ not nat(x) *)
  let nat'' = Predicate.mk_fix (Predicate.Nu) (Ident.Pvar "X") [(Ident.Tvar "x", T_int.SInt)]
               (Formula.mk_and (Formula.mk_atom (Atom.mk_app px [T_int.mk_add (tx) (T_int.one Dummy) Dummy] Dummy) Dummy)
                  (Formula.mk_neg (Formula.mk_atom (Atom.mk_app nat [tx] Dummy) Dummy) Dummy) Dummy) in
  (* (nuX(x).X(x+1) /\ (muY(y).y=0\/Y(y-1))(x))(n) => n >= 0 *)
  let nin = Formula.mk_imply (Formula.mk_atom (Atom.mk_app nat' [tn] Dummy) Dummy)
              (Formula.mk_atom (T_int.mk_geq tn (T_int.zero Dummy) Dummy) Dummy) Dummy |> Convert.Hesutil.hes_of_formula in
  let pip = Formula.mk_imply (Formula.mk_atom (T_int.mk_geq tn (T_int.zero Dummy) Dummy) Dummy)
              (Formula.mk_atom (Atom.mk_app nat' [tn] Dummy) Dummy) Dummy |> Convert.Hesutil.hes_of_formula in
  let pin = Formula.mk_imply (Formula.mk_atom (Atom.mk_app nat'' [tn] Dummy) Dummy)
              (Formula.mk_atom (T_int.mk_geq tn (T_int.zero Dummy) Dummy) Dummy) Dummy |> Convert.Hesutil.hes_of_formula in
  let nip = Formula.mk_imply (Formula.mk_atom (T_int.mk_geq tn (T_int.zero Dummy) Dummy) Dummy)
              (Formula.mk_atom (Atom.mk_app nat'' [tn] Dummy) Dummy) Dummy |> Convert.Hesutil.hes_of_formula in
  let nin_ans = (Core.Set.Poly.empty, Core.Set.Poly.of_list [Ident.Pvar "X"; Ident.Pvar "Y"]) in
  let pip_ans = (Core.Set.Poly.of_list [Ident.Pvar "X"; Ident.Pvar "Y"], Core.Set.Poly.empty) in
  let pin_ans = (Core.Set.Poly.singleton (Ident.Pvar "Y"), Core.Set.Poly.singleton (Ident.Pvar "X")) in
  let nip_ans = (Core.Set.Poly.singleton (Ident.Pvar "X"), Core.Set.Poly.singleton (Ident.Pvar "Y")) in
  let eq (sp, sn) (sp', sn') = Core.Set.Poly.equal sp sp' && Core.Set.Poly.equal sn sn' in
  [
    {name = "negative-in-nagative"; actual = (fun () -> nin |> Constraint.pn_of_hes |> eq nin_ans);
     expected = true };
    {name = "positive-in-positive"; actual = (fun () -> pip |> Constraint.pn_of_hes |> eq pip_ans);
     expected = true };
    {name = "positive-in-nagative"; actual = (fun () -> pin |> Constraint.pn_of_hes |> eq pin_ans);
     expected = true };
    {name = "nagative-in-positive"; actual = (fun () -> nip |> Constraint.pn_of_hes |> eq nip_ans);
     expected = true }
  ]

let _ = run_test_tt_main begin
    "evaluation formula test" >::: (gen_tests eval_formula_test)
  end

let _ = run_test_tt_main begin
    "evaluation term test" >::: (gen_tests eval_term_test)
  end

let _ = run_test_tt_main begin
    "test for extraction from HES" >::: (gen_tests constraint_extraction_test)
  end;
