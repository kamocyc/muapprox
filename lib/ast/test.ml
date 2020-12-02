open OUnit
open Ast
open Ast.Logic
open Testutil

let int_var name = Term.mk_var (Ident.Tvar name) T_int.SInt Dummy

let fml_true = Formula.mk_atom (Atom.mk_true Dummy) Dummy
let fml_false = Formula.mk_atom (Atom.mk_false Dummy) Dummy
(* exists a. a >= 10 *)
let fml_exists = Formula.mk_exists
    [Ident.Tvar "a", T_int.SInt]
    (Formula.mk_atom
       (T_int.mk_gt (int_var "a") (T_int.mk_int (Bigint.of_int 10) Dummy) Dummy) Dummy)
    Dummy
(* a >= 10 -> a * 2 < 20 *)
let fml_math_nosat = Formula.mk_imply
    (Formula.mk_atom (T_int.mk_geq (int_var "a") (T_int.mk_int (Bigint.of_int 10) Dummy) Dummy) Dummy)
    (Formula.mk_atom (T_int.mk_lt
                        (T_int.mk_mult (int_var "a") (T_int.mk_int (Bigint.of_int 2) Dummy) Dummy)
                        (T_int.mk_int (Bigint.of_int 20) Dummy)
                        Dummy) Dummy) Dummy
(* a >= 10 /\ a * 2 >= 20 *)
let fml_math_nosat_neg = Formula.mk_and
    (Formula.mk_atom (T_int.mk_geq (int_var "a") (T_int.mk_int (Bigint.of_int 10) Dummy) Dummy) Dummy)
    (Formula.mk_atom (T_int.mk_geq
                        (T_int.mk_mult (int_var "a") (T_int.mk_int (Bigint.of_int 2) Dummy) Dummy)
                        (T_int.mk_int (Bigint.of_int 20) Dummy)
                        Dummy) Dummy) Dummy

(* simplify in Logic.ml *)
let simplify_tests =
  [
    { name = "nochange"; actual = (fun () -> Formula.simplify fml_true); expected = fml_true; };
    { name = "simpl"; actual = (fun () -> Formula.simplify (Formula.mk_and fml_true fml_exists Dummy)); expected = fml_exists; };
    { name = "recursive"; actual = (fun () -> Formula.simplify (Formula.mk_or fml_exists (Formula.mk_neg (Formula.mk_and fml_false fml_exists Dummy) Dummy) Dummy)); expected = fml_true; };
    { name = "geq_neg"; actual = (fun () -> Formula.simplify_neg fml_math_nosat); expected = fml_math_nosat_neg };
  ]


let _ = run_test_tt_main begin
    "simplify_test" >::: (gen_tests simplify_tests)
  end

let f_pvar = Predicate.Var (Ident.Pvar "F", [T_int.SInt])
let g_pvar = Predicate.Var (Ident.Pvar "G", [T_int.SInt])

let fml_pred_app_f = Formula.mk_atom (
    Atom.mk_app
      f_pvar
      [T_int.zero Dummy]
      Dummy)
    Dummy

let fml_pred_app_g = Formula.mk_atom (
    Atom.mk_app
      g_pvar
      [T_int.zero Dummy]
      Dummy)
    Dummy

let subst_pred_tests =
  [
    {
      (* [true/F X](G 0) -> G 0 *)
      name = "nochange";
      actual = (fun () -> Formula.subst_pred (Ident.Pvar "F") [Ident.Tvar "X", T_int.SInt] fml_true fml_pred_app_g);
      expected = fml_pred_app_g;
    };
    {
      (* [true/F X](F 0) -> true *)
      name = "simple";
      actual = (fun () -> Formula.subst_pred (Ident.Pvar "F") [Ident.Tvar "X", T_int.SInt] fml_true fml_pred_app_f);
      expected = fml_true;
    };
    {
      (* [X = 1/F X](F 1) -> 1 = 1 *)
      name = "replace arg";
      actual = (fun () ->
          Formula.subst_pred
            (Ident.Pvar "F") [Ident.Tvar "X", T_int.SInt]
            (Formula.mk_atom (Atom.mk_app (Predicate.Psym T_bool.Eq) [
                 Term.mk_var (Ident.Tvar "X") T_int.SInt Dummy;
                 T_int.one Dummy;
               ] Dummy) Dummy)
            (Formula.mk_atom (Atom.mk_app f_pvar [T_int.one Dummy] Dummy) Dummy)
        );
      expected = Formula.mk_atom (Atom.mk_app (Predicate.Psym T_bool.Eq) [T_int.one Dummy; T_int.one Dummy] Dummy) Dummy;
    };
  ]

let _ = run_test_tt_main begin
    "subset_pred_test" >::: (gen_tests subst_pred_tests)
  end
