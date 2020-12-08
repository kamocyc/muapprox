
open OUnit
open Ast.Logic
open Smt.Z3interface
open Ast
open Convert

let bool_var name = Term.mk_var (Ident.Tvar name) T_bool.SBool Dummy
let a_bool = bool_var "a"
let b_bool = bool_var "b"
let top_term = T_bool.mk_bool (Atom.True Dummy) Dummy

let body: Formula.t =
  Formula.mk_and
    (Formula.mk_atom
       (T_bool.mk_eq a_bool top_term Dummy)
       Dummy
    )
    (Formula.mk_neg
       (Formula.mk_atom
          (T_bool.mk_eq b_bool top_term Dummy)
          Dummy
       )
       Dummy
    )
    Dummy

let phi: Formula.t =
  Formula.mk_forall
    [
      Ident.Tvar "a", T_bool.SBool;
      Ident.Tvar "b", T_bool.SBool
    ]
    body
    Dummy

let dataset = [
  ("true", Formula.mk_atom (Atom.mk_true Dummy) Dummy);
  ("false", Formula.mk_atom (Atom.mk_false Dummy) Dummy);
  ("forall a:bool, b:bool. (a=\\top) /\\ ~(b=\\top)", phi)
];;

let convert_test () =
  let ctx = Z3.mk_context ["MODEL", "true"] in
  List.iter (fun (desc, phi) ->
      let expr = of_formula ctx Ast.Env.empty Ast.Env.empty phi in
      let phi' = formula_of Ast.Env.empty Ast.Env.empty expr in
      assert_equal ~msg:desc ~printer:Printer.str_of_formula phi phi'
    ) dataset

let _ = run_test_tt_main (
    "convert_test" >:: convert_test
  )

