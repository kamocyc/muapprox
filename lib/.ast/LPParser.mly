%{
  open Logic

  (* Logic Program Parser *)
%}

%token <Bigint.t> INT
%token <string> VAR
%token <string> PVAR
%token PLUS MINUS TIMES DIV
%token EQ NOTEQ NOT GT LT GEQ LEQ COMMA SEMICOLON
%token LPAREN RPAREN
%token ASSUME DECLARE
%token BOT TOP
%token DOT EOF
/* %token FORALL */
%token EXISTS

%left PLUS MINUS TIMES DIV
%nonassoc UNARY

%start parser_main_logic_program
%type <(Logic.Formula.t * Logic.Formula.t) list > parser_main_logic_program
%%

parser_main_logic_program: clauses EOF { $1 }

clauses: list(clause) { $1 }

clause:
  | head DOT { $1, Formula.mk_atom (Atom.mk_true Dummy) Dummy }
  | head ASSUME body DOT { $1, $3 }
  | head DECLARE body DOT { $1, $3 }
  | error {
        let message = Printf.sprintf "clause parse error near characters %d-%d"
                                     (Parsing.symbol_start ())
                                     (Parsing.symbol_end ())
        in failwith message
      }

atoms: separated_list(COMMA, atom) { $1 }

head:
 | atoms { Formula.or_of $1 Dummy }
 | EXISTS vars DOT atoms { Formula.mk_exists $2 (Formula.or_of $4 Dummy) Dummy }

body: atoms { Formula.and_of $1 Dummy }

atom:
  | NOT atom { Formula.mk_neg $2 Dummy }
  | term EQ term { Formula.mk_atom (T_bool.mk_eq $1 $3 Dummy) Dummy }
  | term NOTEQ term { Formula.mk_atom (T_bool.mk_neq $1 $3 Dummy) Dummy }
  | term GT term { Formula.mk_atom (T_int.mk_gt $1 $3 Dummy) Dummy }
  | term LT term { Formula.mk_atom (T_int.mk_lt $1 $3 Dummy) Dummy }
  | term GEQ term { Formula.mk_atom (T_int.mk_geq $1 $3 Dummy) Dummy }
  | term LEQ term { Formula.mk_atom (T_int.mk_leq $1 $3 Dummy) Dummy }
  | TOP { Formula.mk_atom (Atom.mk_true Dummy) Dummy }
  | BOT { Formula.mk_atom (Atom.mk_false Dummy) Dummy }
  | PVAR LPAREN terms RPAREN {
   (* Assuming that every terms are integers (sould be fixed)  *)
   let sorts = List.map (fun _ -> T_int.SInt) $3 in
   let pred = Predicate.Var (Ident.Pvar $1, sorts) in
   Formula.mk_atom (Atom.mk_app pred $3 Dummy) Dummy
   }
  | error {
       let message = Printf.sprintf "atom parse error near characters %d-%d"
                                    (Parsing.symbol_start ())
                                    (Parsing.symbol_end ())
       in failwith message
  }
(*
   let sorts = List.map (Logic.AstUtil.sort_of_term []) $3 in (* BUG *)
*)

term:
 | VAR { Term.mk_var (Ident.Tvar $1) T_int.SInt Dummy (* assume sort is int *) }
 | INT { T_int.mk_int $1 Dummy }
 | MINUS term %prec UNARY { T_int.mk_unary_neg $2 Dummy }
 | term PLUS term { T_int.mk_add $1 $3 Dummy }
 | term TIMES term { T_int.mk_mult $1 $3 Dummy }
 | term MINUS term { T_int.mk_sub $1 $3 Dummy }
 | term DIV term { T_int.mk_div $1 $3 Dummy }

terms : separated_list(COMMA, term) { $1 }

vars : separated_list(COMMA, VAR) { List.map (fun x -> (Ident.Tvar x), T_int.SInt) $1 }

