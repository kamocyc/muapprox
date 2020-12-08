open Ast
open Ast.Logic
open Testutil
open OUnit
open Convert
open Hes

let si = T_int.SInt
let varF = Ident.Pvar "F"
let varG = Ident.Pvar "G"
let varG2 = Ident.Pvar "G2"
let varG3 = Ident.Pvar "G3"
let varX = Ident.Tvar "X"
let varY = Ident.Tvar "Y"
let varZ = Ident.Tvar "Z"
let termX = Term.mk_var varX si Dummy
let termY = Term.mk_var varY si Dummy
let termZ = Term.mk_var varZ si Dummy
let predF = Predicate.mk_var varF [si]
let predG = Predicate.mk_var varG [si]
let predGii = Predicate.mk_var varG [si; si]
let predG2 = Predicate.mk_var varG2 [si]
let predG3 = Predicate.mk_var varG3 [si]

let fx = Formula.mk_atom (Atom.mk_app predF [termX] Dummy) Dummy
let gx = Formula.mk_atom (Atom.mk_app predG [termX] Dummy) Dummy
let g2x = Formula.mk_atom (Atom.mk_app predG2 [termX] Dummy) Dummy
let g3x = Formula.mk_atom (Atom.mk_app predG3 [termX] Dummy) Dummy

let entry_fx = Formula.mk_forall [(varX, si)] fx Dummy

(* forall X. (nuF X. F X) X *)
let ffl_nu =
  Formula.mk_forall [(varX, si)]
    (Formula.mk_atom
       (Atom.mk_app
          (Predicate.mk_fix Predicate.Nu varF [(varX, si)] fx)
          [termX] Dummy)
       Dummy)
    Dummy

(* [F =nu F X], forall X. F X *)
let hes_nu =
  HesLogic.mk_hes
    [HesLogic.mk_func Predicate.Nu varF [(varX, si)] fx]
    entry_fx

(* forall X. (muF X. (F X) \/ ((nuG X. G X) X) /\ ((nuG X. G X) X)) X *)
let ffl_mu_nu_nu_nu =
  let nuG = Formula.mk_atom
      (Atom.mk_app
         (Predicate.mk_fix Predicate.Nu varG [varX, si]
            (Formula.mk_or fx gx Dummy)
         ) [termX]
         Dummy)
      Dummy
  in
  Formula.mk_forall [(varX, si)]
    (Formula.mk_atom
       (Atom.mk_app
          (Predicate.mk_fix Predicate.Mu varF [varX, si]
             (Formula.mk_or
                fx
                (Formula.mk_and (Formula.mk_and nuG nuG Dummy) nuG Dummy)
                Dummy)
          ) [termX]
          Dummy)
       Dummy)
    Dummy

(*
  [
    F(X) =mu (F X) or (G X and G2 X and G3 X);
    G3(X) =nu (F X) or (G3 X);
    G2(X) =nu (F X) or (G2 X);
    G(X) =nu (F X) or (G X);
  ],
  forall X. F X
*)
let hes_mu_nu_nu_nu =
  HesLogic.mk_hes
    [
      (HesLogic.mk_func Predicate.Mu varF [varX, si]
         (Formula.mk_or fx (Formula.mk_and (Formula.mk_and gx g2x Dummy) g3x Dummy) Dummy)
      );
      (HesLogic.mk_func Predicate.Nu varG3 [varX, si] (Formula.mk_or fx g3x Dummy));
      (HesLogic.mk_func Predicate.Nu varG2 [varX, si] (Formula.mk_or fx g2x Dummy));
      (HesLogic.mk_func Predicate.Nu varG [varX, si] (Formula.mk_or fx gx Dummy))
    ]
    entry_fx

(* forall X. (muF X. (nuG Y. G X)(X)) X *)
let ffl_inner_fvar =
  Formula.mk_forall
    [varX, si]
    (Formula.mk_atom
       (Atom.mk_app
          (Predicate.mk_fix
             Predicate.Mu varF [varX, si]
             (Formula.mk_atom
                (Atom.mk_app
                   (Predicate.mk_fix
                      Predicate.Nu varG [varY, si]
                      (Formula.mk_atom
                         (Atom.mk_app
                            predG
                            [termX]
                            Dummy)
                         Dummy))
                   [termX]
                   Dummy)
                Dummy)
          )
          [termX]
          Dummy)
       Dummy)
    Dummy

(* forall X. (muF X. (nuG Y. G X)(X)) X *)
(*
  [
    F(X) =mu G X X
    G(Y, X) =nu G X X
  ],
  forall X. F X
*)
let hes_inner_fvar =
  HesLogic.mk_hes
    [
      HesLogic.mk_func
        Predicate.Mu varF [varX, si]
        (Formula.mk_atom
           (Atom.mk_app predGii [termX; termX] Dummy)
           Dummy);
      HesLogic.mk_func
        Predicate.Nu varG [(varY, si); (varX, si)]
        (Formula.mk_atom
           (Atom.mk_app predGii [termX; termX] Dummy)
           Dummy);
    ]
    entry_fx

let msg expected actual =
  (Printf.sprintf "Expected: %s\n\n" @@ Hesutil.str_of_hes expected)
  ^ (Printf.sprintf "Actual: %s\n\n" @@ Hesutil.str_of_hes actual)

let pp_diff formatter (expected, actual) =
  Format.pp_print_string formatter @@ "\n" ^ msg expected actual

(* hes_of_formula *)
let hes_of_formula_tests =
  [
    {name = "nu"; input = ffl_nu; expected = hes_nu };
    {name = "mu_nu_nu_nu"; input = ffl_mu_nu_nu_nu; expected = hes_mu_nu_nu_nu };
    {name = "inner_fvar"; input = ffl_inner_fvar; expected = hes_inner_fvar};
  ]

(*** Run Tests ***)
let _ = run_test_tt_main begin
    "hes_of_formula" >::: (gen_tests_with_exec ~pp_diff:pp_diff Hesutil.hes_of_formula hes_of_formula_tests)
  end
