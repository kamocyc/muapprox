open OUnit
open Core
open Ast.Logic
open Ast
open Convert

let desugar_dataset = [
  ("atom",
   Formula.mk_atom (Atom.mk_true Dummy) Dummy,
   Formula.mk_atom (Atom.mk_true Dummy) Dummy);

  ("exists x:int. x>0",
   (* exists x:int. x>0 *)
   Formula.mk_exists
     [Ident.Tvar "x", T_int.SInt]
     (Formula.mk_atom
        (Atom.mk_app
           (Predicate.Psym T_int.Gt)
           [
             Term.mk_var (Ident.Tvar "x") (T_int.SInt) Dummy;
             T_int.mk_int (Bigint.of_int 0) Dummy;
           ]
           Dummy)
        Dummy)
     Dummy,
   (*
      (mu #pvar1(x:int). x > 0 \/ X(x+1) \/ X(x-1))(0)
   *)
   Formula.mk_atom
     (Atom.mk_app
        (Predicate.Fixpoint (
            Predicate.Mu,
            Ident.Pvar "#pvar1",
            [Ident.Tvar "x", T_int.SInt],
            Formula.mk_or
              (Formula.mk_or
                 (Formula.mk_atom
                    (Atom.mk_app
                       (Predicate.Psym T_int.Gt)
                       [
                         Term.mk_var (Ident.Tvar "x") T_int.SInt Dummy;
                         T_int.mk_int (Bigint.of_int 0) Dummy;
                       ]
                       Dummy)
                    Dummy)
                 (Formula.mk_atom
                    (Atom.mk_app
                       (Predicate.Var (Ident.Pvar "#pvar1", [T_int.SInt]))
                       [
                         T_int.mk_add
                           (Term.mk_var (Ident.Tvar "x") T_int.SInt Dummy)
                           (T_int.mk_int (Bigint.of_int 1) Dummy)
                           Dummy
                       ]
                       Dummy)
                    Dummy)
                 Dummy)
              (Formula.mk_atom
                 (Atom.mk_app
                    (Predicate.Var (Ident.Pvar "#pvar1", [T_int.SInt]))
                    [
                      T_int.mk_sub
                        (Term.mk_var (Ident.Tvar "x") T_int.SInt Dummy)
                        (T_int.mk_int (Bigint.of_int 1) Dummy)
                        Dummy
                    ]
                    Dummy)
                 Dummy)
              Dummy
          ))
        [T_int.mk_int (Bigint.of_int 0) Dummy]
        Dummy)
     Dummy
  );
]

let desugar_test () =
  List.iter ~f:(fun (desc, phi1, phi2) ->
      assert_equal ~msg:desc ~printer:Printer.str_of_formula
        (Desugar.of_formula phi1)
        (phi2)
    ) desugar_dataset

let int_var name = Term.mk_var (Ident.Tvar name) T_int.SInt Dummy

let print_parse_dataset = [
  ("true", Formula.mk_atom (Atom.mk_true Dummy) Dummy);
  ("exists a. a >= 10",
   Formula.mk_exists
     [Ident.Tvar "a", T_int.SInt]
     (Formula.mk_atom
        (T_int.mk_gt (int_var "a") (T_int.mk_int (Bigint.of_int 10) Dummy) Dummy) Dummy)
     Dummy);
  ("(a >= 10) => a*2 < 20 ",
   Formula.mk_imply
     (Formula.mk_atom (T_int.mk_geq (int_var "a") (T_int.mk_int (Bigint.of_int 10) Dummy) Dummy) Dummy)
     (Formula.mk_atom (T_int.mk_lt
                         (T_int.mk_mult (int_var "a") (T_int.mk_int (Bigint.of_int 2) Dummy) Dummy)
                         (T_int.mk_int (Bigint.of_int 20) Dummy)
                         Dummy) Dummy) Dummy)
]

let print_parse_test () =
  List.iter ~f:(fun (desc, phi) ->
      let str = Printer.str_of_formula phi in
      match Parser.formula_of_str str with
      | Ok phi' ->
        assert_equal ~msg:desc ~printer:Printer.str_of_formula phi phi'
      | Error msg ->
        assert_failure msg
    ) print_parse_dataset


let _ = run_test_tt_main begin
    "convert tests" >::: [
      "desugar test" >:: desugar_test;
      "print/parse test" >:: print_parse_test;
    ]
  end

