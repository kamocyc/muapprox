
%{
open Hflmc2_util
open Hflmc2_syntax
open Raw_program
open Itype
%}

%token <int> INT
%token <string> LIDENT
// %token <string> UIDENT

%token EOF
%token LPAREN  "(" RPAREN  ")"
%token COLON ":"

%token COMMA "," DOT "." 
%token AND
%token ENV
%token TRANSITION PRIORITY

%token TINT TARROW "->"

//%left STAR
//%nonassoc NEG

%type <(Itype.automaton) option> main
%type <Itype.itype_env> env
%start main

%%

main:
| env transition priority EOF     { Some (Some $1, $2, $3) }
| transition priority EOF     { Some (None, $1, $2) }

transition:
| TRANSITION trans_rule+ { mk_transition_rules $2 }

trans_rule:
| LIDENT LIDENT "->" LIDENT { mk_transition_rule $1 $2 $4 }
| LIDENT LIDENT "->" LIDENT DOT { mk_transition_rule $1 $2 $4 }

priority:
| PRIORITY priority_rule+ { $2 }

priority_rule:
| LIDENT "->" INT { mk_priority_rule $1 $3 }
| LIDENT "->" INT DOT { mk_priority_rule $1 $3 }

(******************************************************************************)
(* Util                                                                       *)
(******************************************************************************)

env:
| ENV env_rule+ { $2 }

env_rule:
| LIDENT ":" env_argty_item { Id.gen ~name:$1 (), $3 }

env_ty:
| LIDENT { ITState (State $1) }
| env_argty "->" env_ty { ITFunc ($1, $3) }

env_argty:
| TINT { IAInt }
| separated_list(AND, env_argty_item) { IAInter $1 }

env_argty_item:
| "(" env_ty "," INT ")" { $2, $4 }
