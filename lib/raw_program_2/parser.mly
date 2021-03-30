
%{
open Hflmc2_util
open Hflmc2_syntax
open Program_raw
%}

%token <int> INT
%token <string> LIDENT
// %token <string> UIDENT

%token EOF
%token LPAREN  "(" RPAREN  ")"
%token LANGRE  "<" RANGRE  ">"
%token TRUE FALSE
%token COLON ":"
%token SEMICOLON ";"
%token LET "let" IN "in"
%token IF "if" THEN "then" ELSE "else" EVENT "event"
%token UNIT "()"

%token LAMBDA DOT "." 
%token PLUS  "+" MINUS "-" // NEG
%token STAR "*"
//%token SLASH "/" PERCENT "%"
%token EQ "=" NEQ "<>" LE "<=" GE ">="
%token AND "&&" OR "||"

%token TUNIT TINT TARROW "->"

%right OR
%right AND
%left PLUS MINUS
//%left STAR
//%nonassoc NEG

%type <Program_raw.raw_program> program
%type <Program_raw.ptype> abstraction_ty
%start program

%%

program:
| function_definition+ EOF { $1 }

function_definition:
| "let" lvar arg* "=" function_body
    { { var  = $2, None
      ; args = $3
      ; body = $5
      }
    }
| "let" "()" "=" function_body
    { { var  = "", None
      ; args = []
      ; body = $4
      }
    }

arg:
| lvar { mk_arg $1 None }
| "(" lvar ":" argty ")" { mk_arg $2 (Some $4) }

argty:
| abstraction_ty     { $1 }

function_body:
| cps_expr { $1 }

cps_expr:
| "if" and_or_expr "then" cps_expr "else" cps_expr { mk_if $2 $4 $6 }
| "if" "*" "then" cps_expr "else" cps_expr { mk_nondet $4 $6 None }
| "if" LANGRE LIDENT RANGRE "*" "then" cps_expr "else" cps_expr { mk_nondet $7 $9 (Some $3) }
| "event" LIDENT ";" cps_expr { mk_event $2 $4 }
| "()" { PUnit }
| "let" lvar "=" cps_expr "in" cps_expr { mk_let ($2, None) $4 $6 }
| "let" lvar ":" argty "=" cps_expr "in" cps_expr { mk_let ($2, Some $4) $6 $8 }
| simple_expr { $1 }
| application { $1 }

application:
| simple_expr simple_expr+ { mk_apps $1 $2 }

and_or_expr:
| and_or_expr "&&" and_or_expr  { mk_ands [$1;$3] }
| and_or_expr "||" and_or_expr  { mk_ors  [$1;$3] }
| bool                          { mk_bool  $1 }
| pred_expr                     { $1 }

pred_expr:
| arith_expr pred arith_expr { mk_pred $2 $1 $3 }

simple_expr:
| INT  { mk_int   $1 }
| "*"  { mk_nondet_int None }
| LANGRE LIDENT RANGRE "*"  { mk_nondet_int (Some $2) }
| lvar { mk_var $1 }
| "(" LAMBDA arg* DOT cps_expr ")" { mk_lambda $3 $5 }
| "(" cps_expr ")" { $2 }
| "(" arith_expr ")" { $2 }
| "(" "-" arith_expr ")" { mk_op Arith.Sub [mk_int 0;$3] }

arith_expr:
| simple_expr { $1 }
| arith_expr op arith_expr { mk_op $2  [$1;$3] }

(******************************************************************************)
(* Predicate                                                                  *)
(******************************************************************************)

abstraction_ty:
| TUNIT  { TUnit }
| TINT   { TInt  }
| "(" abstraction_ty ")" { $2 }
| abstraction_ty "->" abstraction_ty
    { 
      TFunc($1, $3)
    }

(******************************************************************************)
(* Util                                                                       *)
(******************************************************************************)

%inline op:
| "+" { Arith.Add  }
| "-" { Arith.Sub  }
//| "*" { Arith.Mult }
//| "/" { Arith.Div }
//| "%" { Arith.Mod }

pred:
| "="  { Formula.Eq  }
| "<>" { Formula.Neq }
| "<=" { Formula.Le  }
| ">=" { Formula.Ge  }
| "<"  { Formula.Lt  }
| ">"  { Formula.Gt  }

lvar:
(* Adhoc way. Because hoice complains the use of _ as an identity *)
| LIDENT { if $1 = "_" then "replaced!" else $1 }

bool:
| TRUE  { true  }
| FALSE { false }
