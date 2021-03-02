
%{
open Hflmc2_util
open Hflmc2_syntax
open Raw_program
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
%token LET "let"
%token IF "if" THEN "then" ELSE "else" EVENT "event"
%token UNIT "()"

%token COMMA ","
%token PLUS  "+" MINUS "-" STAR  "*" SLASH "/" PERCENT "%" NEG
%token EQ "=" NEQ "<>" LE "<=" GE ">="
%token AND "&&" OR "||"
%token ENV HES
%token TRANSITION PRIORITY INITIAL

%token TUNIT TINT TARROW "->"

%right OR
%right AND
%left PLUS MINUS
%left STAR
%nonassoc NEG

%type <Raw_program.hes * (Itype.itype_env * Itype.state * Itype.transition_rule list * Itype.priority_rule list) option> main
%type <Hflmc2_syntax.Type.simple_ty> abstraction_ty
%type <Hflmc2_syntax.Type.simple_argty> abstraction_argty
%type <Itype.itype_env> env
%start main

%%

main:
// | hes EOF     { $1, None }
| hes env initial transition priority EOF     { $1, Some ($2, $3, $4, $5) }

initial:
| INITIAL LIDENT { Itype.State $2 }

transition:
| TRANSITION trans_rule+ { $2 }

trans_rule:
| "(" LIDENT "," LIDENT ")" "->" LIDENT { Itype.mk_transition_rule $2 $4 $7 }

priority:
| PRIORITY priority_rule+ { $2 }

priority_rule:
| LIDENT "->" INT { Itype.mk_priority_rule $1 $3 }

(******************************************************************************)
(* HES                                                                        *)
(******************************************************************************)

hes:
| HES hflz_rule+ { $2 }

hflz_rule:
| "let" lvar arg* "=" hflz
    { { var  = $2
      ; args = $3
      ; body = $5
      }
    }
| "let" "()" "=" hflz
    { { var  = ""
      ; args = []
      ; body = $4
      }
    }

arg:
| "(" lvar ":" argty ")" { mk_arg $2 $4 }

argty:
| abstraction_ty     { Type.TySigma $1 }
| abstraction_argty  { $1 }

hflz:
| and_or_expr { $1 }

and_or_expr:
| and_or_expr "&&" and_or_expr  { mk_ands [$1;$3] }
| and_or_expr "||" and_or_expr  { mk_ors  [$1;$3] }
| pred_expr                     { $1 }
| "if" and_or_expr "then" hflz "else" hflz { mk_if $2 $4 $6 }
| "if" "*" "then" hflz "else" hflz { mk_nondet $4 $6 }
| "event" LIDENT ";" hflz { mk_event $2 $4 }


pred_expr:
| arith_expr                 { $1               }
| arith_expr pred arith_expr { mk_pred $2 $1 $3 }

arith_expr:
| app_expr                 { $1                }
| arith_expr op arith_expr { mk_op $2  [$1;$3] }
| "-" arith_expr %prec NEG { mk_op Arith.Sub [mk_int 0;$2] }

app_expr:
| atom atom* { mk_apps $1 $2 }

atom:
| "()" { PUnit }
| INT  { mk_int   $1 }
| bool { mk_bool  $1 }
| lvar { mk_var   $1 }
// | uvar { mk_var   $1 }
| "(" hflz ")" { $2 }

(******************************************************************************)
(* Predicate                                                                  *)
(******************************************************************************)

// env:
// | START_ENV assignment* { $2 }

// assignment:
// | uvar ":" abstraction_ty DOT { $1, $3 }

abstraction_ty:
| TUNIT                    { Type.TyBool ()   }
| abstraction_argty "->" abstraction_ty
    { let x = Id.{ name="_"; id=(-1); ty=$1 } in
      Type.TyArrow(x, $3)
    }
// | TBOOL "[" separated_list(";", predicate) "]" { Type.TyBool($3) }
// | lvar ":" abstraction_argty "->" abstraction_ty
//     { let x = Id.{ name=$1; id=(-1); ty=$3 } in
//       Type.TyArrow(x, $5)
//     }

abstraction_argty:
| TINT                   { Type.TyInt      }
| "(" abstraction_ty ")" { Type.TySigma $2 }

// predicate:
// | and_or_predicate { $1 }

// and_or_predicate:
// | and_or_predicate "&&" and_or_predicate { Formula.mk_ands [$1;$3] }
// | and_or_predicate "||" and_or_predicate { Formula.mk_ors  [$1;$3] }
// | a_predicate                            { $1                      }

// a_predicate:
// | atom_predicate { $1 }
// | arith pred arith { Formula.mk_pred $2 [$1;$3] }

// arith:
// | atom_arith          { $1                                  }
// | arith op arith      { Arith.mk_op $2  [$1;$3]             }
// | "-" arith %prec NEG { Arith.mk_op Sub Arith.[mk_int 0;$2] }

// atom_arith:
// | "(" arith ")" { $2                                          }
// | INT           { Arith.mk_int $1                             }
// | lvar          { let x = Id.{ name=$1; ty=`Int; id=(-1) } in
//                   Arith.mk_var x
//                 }

// atom_predicate:
// | TRUE  { Formula.Bool true  }
// | FALSE { Formula.Bool false }
// | "(" predicate ")"     { $2 }


(******************************************************************************)
(* Util                                                                       *)
(******************************************************************************)

%inline op:
| "+" { Arith.Add  }
| "-" { Arith.Sub  }
| "*" { Arith.Mult }
| "/" { Arith.Div }
| "%" { Arith.Mod }

pred:
| "="  { Formula.Eq  }
| "<>" { Formula.Neq }
| "<=" { Formula.Le  }
| ">=" { Formula.Ge  }
| "<"  { Formula.Lt  }
| ">"  { Formula.Gt  }


// lambdas:
// | lambda* { List.concat $1 }
// lambda:
// | LAMBDA lvar* "." { $2 }

lvar:
(* Adhoc way. Because hoice complains the use of _ as an identity *)
| LIDENT { if $1 = "_" then "replaced!" else $1 }

// uvar:
// | UIDENT { $1 }

bool:
| TRUE  { true  }
| FALSE { false }

env:
| ENV env_rule+ { $2 }

env_rule:
| LIDENT ":" env_argty_item { Id.gen ~name:$1 (), $3 }

env_ty:
| LIDENT { Itype.ITState (Itype.State $1) }
| env_argty "->" env_ty { Itype.ITFunc ($1, $3) }

env_argty:
| TINT { Itype.IAInt }
| separated_list(AND, env_argty_item) { Itype.IAInter $1 }

env_argty_item:
| "(" env_ty "," INT ")" { $2, $4 }
