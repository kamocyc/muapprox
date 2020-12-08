%{
  open Ast
  open Ast.Logic
  open HesLogic
%}

%token CORON INT BOOL REAL
%token LPAREN RPAREN EOF
%token <Ast.Logic.Predicate.fixpoint> EQFIX
%token <Ast.Logic.Formula.binder> BINDER
%token DOT SEMI
%token NOT
%token AND OR IMPLY IFF
%token MINUS ADD MULT DIV MOD
%token <Ast.Logic.pred_sym> PREDSYM
%token <int> INTL
%token TRUE FALSE
%token WHERE
%token <string> ID

%start toplevel
%type <HesLogic.hes> toplevel
%%

/*
;; forall x. F1 x
;; s.t.
;; F1 (x: int): bool =nu G1 x /\ (x <= 5 => F2 x) /\ (x <= 5 => F1 (x + 1)) /\ (x > 5 => F1 (x + 1));
;; F2 (x: int): bool =nu G2 x /\ (x <= 2 => F1 x) /\ (x > 2 => F2 (x-1));
;; G1 (x: int): bool =mu x >= 1 \/ (x <= 5 /\ G2 x) \/ (x <= 5 => G1 (x + 1)) /\ (x > 5 => G1 (x + 1));
;; G2 (x: int): bool =mu x >= 1 \/ (x <= 2 => G1 x) /\ (x > 2 => G2 (x-1));
*/

toplevel:
    entry=Formula WHERE funcs=Funs EOF { HesLogic.mk_hes funcs entry }

Funs:
    f=Fun SEMI funs=Funs { f :: funs }
  | f=Fun SEMI { [f] }

Fun:
    funname=ID bounds=Bounds CORON BOOL fix=EQFIX body=Formula {
      mk_func fix (Ident.Pvar funname) bounds body
    }

/* Ast.Logic.Formula.t */
/* not including LetRec */
Formula:
    fml=FormulaBinder { fml }

FormulaBinder:
    binder=BINDER bounds=Bounds DOT body=Formula { Formula.mk_bind binder bounds body Dummy }
  | fml=FormulaIff { fml }

FormulaIff:
    left=FormulaImply IFF right=FormulaImply { Formula.mk_iff left right Dummy }
  | fml=FormulaImply { fml }

FormulaImply:
    left=FormulaOr IMPLY right=FormulaImply { Formula.mk_imply left right Dummy }
  | fml=FormulaOr { fml }

FormulaOr:
    left=FormulaAnd OR right=FormulaOr { Formula.mk_or left right Dummy }
  | fml=FormulaAnd { fml }

FormulaAnd:
    left=FormulaNeg AND right=FormulaAnd { Formula.mk_and left right Dummy }
  | fml=FormulaNeg { fml }

FormulaNeg:
    NOT fml=FormulaNegParen { Formula.mk_neg fml Dummy }
  | fml=FormulaAtom { fml }

FormulaNegParen:
    NOT fml=FormulaNegParen { Formula.mk_neg fml Dummy }
  | LPAREN fml=Formula RPAREN { fml }

FormulaAtom:
    atom=Atom { Formula.mk_atom atom Dummy }
  | LPAREN fml=Formula RPAREN { fml }


/* Ast.Logic.Atom.t */
Atom:
    funname=ID args=AtomAppArgs { Atom.mk_app (Predicate.mk_var (Ident.Pvar funname) []) args Dummy }
  | atom=T_bool { atom }
  | TRUE { True Dummy }
  | FALSE { False Dummy }

AtomAppArgs:
    { [] }
  | arg=T_intAtom args=AtomAppArgs { arg :: args }


/* Ast.Logic.Term.t */
/* Ast.Logic.T_int */
/* Term:
    t=T_int { t } */

T_int:
    t=T_intAddSub { t }

T_intAddSub:
    t=T_intMultDivMod { t }
  | t1=T_intMultDivMod ADD t2=T_intAddSub { T_int.mk_add t1 t2 Dummy }
  | t1=T_intMultDivMod MINUS t2=T_intAddSub { T_int.mk_sub t1 t2 Dummy }

T_intMultDivMod:
    t=T_intNeg { t }
  | t1=T_intNeg MULT t2=T_intMultDivMod { T_int.mk_mult t1 t2 Dummy }
  | t1=T_intNeg DIV t2=T_intMultDivMod { T_int.mk_div t1 t2 Dummy }
  | t1=T_intNeg MOD t2=T_intMultDivMod { T_int.mk_mod t1 t2 Dummy }

T_intNeg:
    t=T_intAtom { t }
  | MINUS t=T_intNeg { T_int.mk_unary_neg t Dummy }

T_intAtom:
    LPAREN t=T_int RPAREN { t }
  | n=INTL { T_int.mk_int (Bigint.of_int n) Dummy }
  | varname=ID { Term.mk_var (Ident.Tvar varname) T_int.SInt Dummy }

/* Ast.Logic.T_bool */
T_bool:
    t1=T_int op=PREDSYM t2=T_int { Atom.mk_app (Predicate.mk_psym op) [t1; t2] Dummy }


/* Ast.Logic.Predicate.t */
/* not including Fixpoint */
/* Predicate.Psym is dealt with by T_bool */
/* Predicate:
    varname=ID { Predicate.mk_var (Ident.Pvar varname) [] } */


/* Ast.Logic.Sort.t */
Sort:
    INT { T_int.SInt }
  | BOOL { T_bool.SBool }
  | REAL { T_int.SReal }

/* Bounds */
Bounds:
    { [] }
  | LPAREN varname=ID CORON sort=Sort RPAREN bounds=Bounds {
    (Ident.Tvar varname, sort) :: bounds
  }