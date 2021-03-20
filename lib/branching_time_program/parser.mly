
%{
  open Hflmc2_syntax
  open Raw_horsz
%}

%token <int> INT
%token <string> IDENT

%token EOF
%token LPAREN  "(" RPAREN  ")"
%token LANGRE  "<" RANGRE  ">"
%token COLON ":"
%token IF "if" THEN "then" ELSE "else"

%token COMMA "," DOT "." 
%token PLUS  "+" MINUS "-"
// %token STAR "*"
%token EQ "=" NEQ "<>" LE "<=" GE ">="
%token AND "&&" OR "||"
%token RANK GRAMMAR
%token TRANSITION PRIORITY

%token TUNIT TINT TARROW "->"

%right OR
%right AND
%left PLUS MINUS

%type <(string * int) list * Raw_horsz.raw_program * Raw_horsz.automaton> main
%type <(string * int) list> ranks_entry
%type <Raw_horsz.raw_program> grammar
%type <Raw_horsz.ata_trans> ata_rule
%type <Raw_horsz.preformula> ata_formula
%type <Raw_horsz.ata_priority> priority
%type <Hflmc2_syntax.Type.simple_ty> abstraction_ty
%type <Hflmc2_syntax.Type.simple_argty> abstraction_argty
%start main

%%

main:
| ranks_entry grammar automaton EOF     { ($1, $2, $3) }
  
(******************************************************************************)
(* GRAMMAR                                                                        *)
(******************************************************************************)

ranks_entry:
| RANK rank+ { $2 } 

rank:
| var "->" INT DOT { ($1,$3) }
  
grammar:
| GRAMMAR grammar_definition+ { $2 }

grammar_definition:
| var arg* "->" grammar_body DOT
  { { var  = $1, None
    ; args = $2
    ; body = $4
    }
  }

arg:
| "(" var ":" argty ")" { mk_arg $2 (Some $4) }
| var { mk_arg $1 None }

argty:
| abstraction_ty     { Type.TySigma ($1) }
| abstraction_argty  { $1 }

grammar_body:
| cps_expr { $1 }

cps_expr:
| "if" and_or_expr "then" cps_expr "else" cps_expr { mk_if $2 $4 $6 }
| simple_expr { $1 }
| application { $1 }

application:
| simple_expr simple_expr+ { mk_apps $1 $2 }

and_or_expr:
| and_or_expr "&&" and_or_expr  { mk_ands [$1;$3] }
| and_or_expr "||" and_or_expr  { mk_ors  [$1;$3] }
| pred_expr                     { $1 }

pred_expr:
| arith_expr pred arith_expr { mk_pred $2 $1 $3 }

simple_expr:
| INT  { mk_int   $1 }
| var { mk_var $1 }
| "(" cps_expr ")" { $2 }
| "(" arith_expr ")" { $2 }
| "(" "-" arith_expr ")" { mk_op Arith.Sub [mk_int 0;$3] }

arith_expr:
| simple_expr { $1 }
| arith_expr op arith_expr { mk_op $2  [$1;$3] }

(******************************************************************************)
(* Type                                                                       *)
(******************************************************************************)

abstraction_ty:
| TUNIT                    { Type.TyBool () }
| abstraction_argty "->" abstraction_ty
    { 
      TyArrow({Id.name=""; id=0; ty=$1}, $3)
    }
  
abstraction_argty:
| TINT                   { Type.TyInt }
| TUNIT                  { Type.TySigma (Type.TyBool ()) }
| "(" abstraction_ty ")" { Type.TySigma ($2)   }


(******************************************************************************)
(* Automaton                                                                  *)
(******************************************************************************)

automaton:
  | TRANSITION ata_rule+ PRIORITY priority+ { ($2,$4) }

ata_rule:
  | var var "->" ata_formula DOT { ($1, $2), $4 }

ata_formula:
  | var { FConst($1) }
  | "(" INT COMMA var ")" { FVar ($2,$4) }
  | ata_formula AND ata_formula { FAnd ($1,$3) }
  | ata_formula OR ata_formula  { FOr  ($1,$3) }
  | "(" ata_formula ")"   { $2 }

priority:
  | var "->" INT DOT { ($1,$3) }

(******************************************************************************)
(* Util                                                                       *)
(******************************************************************************)

%inline op:
| "+" { Arith.Add  }
| "-" { Arith.Sub  }

pred:
| "="  { Formula.Eq  }
| "<>" { Formula.Neq }
| "<=" { Formula.Le  }
| ">=" { Formula.Ge  }
| "<"  { Formula.Lt  }
| ">"  { Formula.Gt  }

var:
(* Adhoc way. Because hoice complains the use of _ as an identity *)
| IDENT { if $1 = "_" then "replaced!" else $1 }
