open OUnit
open Ast
open Ast.Logic
open Testutil
open Hes

let int_var name = Term.mk_var (Ident.Tvar name) T_int.SInt Dummy
let pred_var name = Predicate.Var ((Ident.Pvar name), [T_int.SInt])

(*** HesLogic.ml ***)
let fml_true = Formula.mk_atom (Atom.mk_true Dummy) Dummy
let fml_false = Formula.mk_atom (Atom.mk_false Dummy) Dummy

(** HES **)
let hes_empty_true = HesLogic.mk_hes [] fml_true
let hes_empty_false = HesLogic.mk_hes [] fml_false
(* forall X. F X *)
let varF = pred_var "F"
let varG = pred_var "G"
let varX = int_var "X"
let varY = int_var "Y"
let entry_forall = Formula.mk_forall [Ident.Tvar "X", T_int.SInt] (Formula.mk_atom (Atom.mk_app varF [varX] Dummy) Dummy) Dummy
let entry_exists = Formula.mk_exists [Ident.Tvar "X", T_int.SInt] (Formula.mk_atom (Atom.mk_app varF [varX] Dummy) Dummy) Dummy
(* forall X. F X; F X =nu F (X * 2) *)
let hes_nu = HesLogic.mk_hes
    [
      Predicate.Nu, (Ident.Pvar "F"), [Ident.Tvar "X", T_int.SInt],
      Formula.mk_atom (Atom.mk_app varF [T_int.mk_mult varX (T_int.mk_int (Bigint.of_int 2) Dummy) Dummy] Dummy) Dummy
    ]
    entry_forall
(* exists X. F X; F X =mu F (X * 2) *)
let hes_mu = HesLogic.mk_hes
    [
      Predicate.Mu, (Ident.Pvar "F"), [Ident.Tvar "X", T_int.SInt],
      Formula.mk_atom (Atom.mk_app varF [T_int.mk_mult varX (T_int.mk_int (Bigint.of_int 2) Dummy) Dummy] Dummy) Dummy
    ]
    entry_exists
(* forall X. F X; F X =nu X >= 5 -> G X; G X =nu X >= 5 /\ (G (X - 1) \/ G (X + 1)) *)
let hes_nunu = HesLogic.mk_hes
    [
      (
        Predicate.Nu, (Ident.Pvar "F"), [Ident.Tvar "X", T_int.SInt],
        Formula.mk_imply
          (Formula.mk_atom (T_int.mk_geq varX (T_int.mk_int (Bigint.of_int 5) Dummy) Dummy) Dummy)
          (Formula.mk_atom (Atom.mk_app varG [varX] Dummy) Dummy) Dummy
      );
      (
        Predicate.Nu, (Ident.Pvar "G"), [Ident.Tvar "X", T_int.SInt],
        Formula.mk_and
          (Formula.mk_atom (T_int.mk_geq varX (T_int.mk_int (Bigint.of_int 5) Dummy) Dummy) Dummy)
          (Formula.mk_or
             (Formula.mk_atom (Atom.mk_app varG [T_int.mk_sub varX (T_int.mk_int (Bigint.of_int 1) Dummy) Dummy] Dummy) Dummy)
             (Formula.mk_atom (Atom.mk_app varG [T_int.mk_add varX (T_int.mk_int (Bigint.of_int 1) Dummy) Dummy] Dummy) Dummy)
             Dummy
          ) Dummy
      )
    ]
    entry_forall
(* exists X. F X; F X =mu X >= 5 /\ G X; G X =mu X < 5 \/ (G (X - 1) /\ G (X + 1)) *)
let hes_mumu = HesLogic.mk_hes
    [
      (
        Predicate.Mu, (Ident.Pvar "F"), [Ident.Tvar "X", T_int.SInt],
        Formula.mk_and
          (Formula.mk_atom (T_int.mk_geq varX (T_int.mk_int (Bigint.of_int 5) Dummy) Dummy) Dummy)
          (Formula.mk_atom (Atom.mk_app varG [varX] Dummy) Dummy) Dummy
      );
      (
        Predicate.Mu, (Ident.Pvar "G"), [Ident.Tvar "X", T_int.SInt],
        Formula.mk_or
          (Formula.mk_atom (T_int.mk_lt varX (T_int.mk_int (Bigint.of_int 5) Dummy) Dummy) Dummy)
          (Formula.mk_and
             (Formula.mk_atom (Atom.mk_app varG [T_int.mk_sub varX (T_int.mk_int (Bigint.of_int 1) Dummy) Dummy] Dummy) Dummy)
             (Formula.mk_atom (Atom.mk_app varG [T_int.mk_add varX (T_int.mk_int (Bigint.of_int 1) Dummy) Dummy] Dummy) Dummy)
             Dummy
          ) Dummy
      )
    ]
    entry_exists
(* forall X. F X; F X =nu (X > 0 => G (X + 1)) /\ (X <= 0 => F (X - 1)); G X =mu (X >= 10 => F (X - 10)) /\ (X < 10 => F X) *)
let hes_numu = HesLogic.mk_hes
    [
      (
        Predicate.Nu, (Ident.Pvar "F"), [Ident.Tvar "X", T_int.SInt],
        Formula.mk_and
          (
            Formula.mk_imply
              (Formula.mk_atom (T_int.mk_gt varX (T_int.mk_int (Bigint.of_int 0) Dummy) Dummy) Dummy)
              (Formula.mk_atom (Atom.mk_app varG [T_int.mk_add varX (T_int.mk_int (Bigint.of_int 1) Dummy) Dummy] Dummy) Dummy)
              Dummy
          )
          (
            Formula.mk_imply
              (Formula.mk_atom (T_int.mk_leq varX (T_int.mk_int (Bigint.of_int 0) Dummy) Dummy) Dummy)
              (Formula.mk_atom (Atom.mk_app varG [T_int.mk_sub varX (T_int.mk_int (Bigint.of_int 1) Dummy) Dummy] Dummy) Dummy)
              Dummy
          )
          Dummy
      );
      (
        Predicate.Mu, (Ident.Pvar "G"), [Ident.Tvar "X", T_int.SInt],
        Formula.mk_and
          (
            Formula.mk_imply
              (Formula.mk_atom (T_int.mk_geq varX (T_int.mk_int (Bigint.of_int 10) Dummy) Dummy) Dummy)
              (Formula.mk_atom (Atom.mk_app varF [T_int.mk_sub varX (T_int.mk_int (Bigint.of_int 10) Dummy) Dummy] Dummy) Dummy)
              Dummy
          )
          (
            Formula.mk_imply
              (Formula.mk_atom (T_int.mk_lt varX (T_int.mk_int (Bigint.of_int 10) Dummy) Dummy) Dummy)
              (Formula.mk_atom (Atom.mk_app varF [varX] Dummy) Dummy)
              Dummy
          )
          Dummy
      )
    ]
    entry_forall
(* exists X. F X; F X =nu (X > 0 /\ G (X + 1)) \/ (X <= 0 /\ F (X - 1)); G X =nu (X >= 10 /\ F (X - 10)) \/ (X < 10 /\ F X) *)
let hes_munu = HesLogic.mk_hes
    [
      (
        Predicate.Mu, (Ident.Pvar "F"), [Ident.Tvar "X", T_int.SInt],
        Formula.mk_or
          (
            Formula.mk_and
              (Formula.mk_atom (T_int.mk_gt varX (T_int.mk_int (Bigint.of_int 0) Dummy) Dummy) Dummy)
              (Formula.mk_atom (Atom.mk_app varG [T_int.mk_add varX (T_int.mk_int (Bigint.of_int 1) Dummy) Dummy] Dummy) Dummy)
              Dummy
          )
          (
            Formula.mk_and
              (Formula.mk_atom (T_int.mk_leq varX (T_int.mk_int (Bigint.of_int 0) Dummy) Dummy) Dummy)
              (Formula.mk_atom (Atom.mk_app varG [T_int.mk_sub varX (T_int.mk_int (Bigint.of_int 1) Dummy) Dummy] Dummy) Dummy)
              Dummy
          )
          Dummy
      );
      (
        Predicate.Nu, (Ident.Pvar "G"), [Ident.Tvar "X", T_int.SInt],
        Formula.mk_or
          (
            Formula.mk_and
              (Formula.mk_atom (T_int.mk_geq varX (T_int.mk_int (Bigint.of_int 10) Dummy) Dummy) Dummy)
              (Formula.mk_atom (Atom.mk_app varF [T_int.mk_sub varX (T_int.mk_int (Bigint.of_int 10) Dummy) Dummy] Dummy) Dummy)
              Dummy
          )
          (
            Formula.mk_and
              (Formula.mk_atom (T_int.mk_lt varX (T_int.mk_int (Bigint.of_int 10) Dummy) Dummy) Dummy)
              (Formula.mk_atom (Atom.mk_app varF [varX] Dummy) Dummy)
              Dummy
          )
          Dummy
      )
    ]
    entry_exists

(* is_onlymu, is_onlynu *)
let is_onlymu_tests =
  [
    { name = "nu"; actual = (fun () -> HesLogic.is_onlymu hes_nu); expected = false; };
    { name = "mu"; actual = (fun () -> HesLogic.is_onlymu hes_mu); expected = true; };
    { name = "nunu"; actual = (fun () -> HesLogic.is_onlymu hes_nunu); expected = false; };
    { name = "mumu"; actual = (fun () -> HesLogic.is_onlymu hes_mumu); expected = true; };
    { name = "numu"; actual = (fun () -> HesLogic.is_onlymu hes_numu); expected = false; };
    { name = "munu"; actual = (fun () -> HesLogic.is_onlymu hes_munu); expected = false; };
    { name = "empty"; actual = (fun () -> HesLogic.is_onlymu hes_empty_true); expected = true; };
  ]
let is_onlynu_tests =
  [
    { name = "nu"; actual = (fun () -> HesLogic.is_onlynu hes_nu); expected = true; };
    { name = "mu"; actual = (fun () -> HesLogic.is_onlynu hes_mu); expected = false; };
    { name = "nunu"; actual = (fun () -> HesLogic.is_onlynu hes_nunu); expected = true; };
    { name = "mumu"; actual = (fun () -> HesLogic.is_onlynu hes_mumu); expected = false; };
    { name = "numu"; actual = (fun () -> HesLogic.is_onlynu hes_numu); expected = false; };
    { name = "munu"; actual = (fun () -> HesLogic.is_onlynu hes_munu); expected = false; };
    { name = "empty"; actual = (fun () -> HesLogic.is_onlynu hes_empty_true); expected = true; };
  ]

(* get_dual_hes *)
(* let get_dual_hes_tests =
   [
    { name = "nu"; actual = (fun () -> HesLogic.get_dual_hes hes_nu); expected = HesLogic.simplify hes_mu; };
    { name = "mu"; actual = (fun () -> HesLogic.get_dual_hes hes_mu); expected = HesLogic.simplify hes_nu; };
    { name = "nunu"; actual = (fun () -> HesLogic.get_dual_hes hes_nunu); expected = HesLogic.simplify hes_mumu; };
    { name = "mumu"; actual = (fun () -> HesLogic.get_dual_hes hes_mumu); expected = HesLogic.simplify hes_nunu; };
    { name = "numu"; actual = (fun () -> HesLogic.get_dual_hes hes_numu); expected = HesLogic.simplify hes_munu; };
    { name = "munu"; actual = (fun () -> HesLogic.get_dual_hes hes_munu); expected = HesLogic.simplify hes_numu; };
    { name = "empty"; actual = (fun () -> HesLogic.get_dual_hes hes_empty_true); expected = HesLogic.simplify hes_empty_false; };
   ] *)

(*** Run Tests ***)
let _ = run_test_tt_main begin
    "is_onlymu" >::: (gen_tests is_onlymu_tests)
  end

let _ = run_test_tt_main begin
    "is_onlynu" >::: (gen_tests is_onlynu_tests)
  end

(* let _ = run_test_tt_main begin
    "get_dual_hes" >::: (gen_tests get_dual_hes_tests)
   end *)
