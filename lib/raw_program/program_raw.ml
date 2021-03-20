open Common_type

type ptype = TInt | TBool | TUnit | TFunc of ptype * ptype | TVar of unit Hflmc2_syntax.Id.t
[@@deriving eq,ord,show]

let rec show_ptype = function
  | TInt -> "int"
  | TBool -> "bool"
  | TUnit -> "unit"
  | TFunc (p1, p2) -> "(" ^ show_ptype p1 ^ "->" ^ show_ptype p2 ^ ")"
  | TVar id -> Hflmc2_syntax.Id.to_string id

type 'a raw_expression_gen =
    PUnit
  | PVar of 'a
  | PIf of 'a raw_expression_gen * 'a raw_expression_gen * 'a raw_expression_gen
  | PEvent of program_event * 'a raw_expression_gen
  | PNonDet of 'a raw_expression_gen * 'a raw_expression_gen
  | PApp of 'a raw_expression_gen * 'a raw_expression_gen
  | AInt of int
  | AOp of arith_op * 'a raw_expression_gen list
  | Pred of pred_op * 'a raw_expression_gen list 
  | And of 'a raw_expression_gen * 'a raw_expression_gen
  | Or of 'a raw_expression_gen * 'a raw_expression_gen
  | Bool of bool
  | PLambda of 'a list * 'a raw_expression_gen
  | PLet of 'a * 'a raw_expression_gen * 'a raw_expression_gen
  | ANonDet
  [@@deriving eq,ord,show]

type raw_expression = (string * ptype option) raw_expression_gen
[@@deriving eq,ord,show]

type 'a raw_function_gen = {
  var: 'a;
  args: 'a list;
  body: 'a raw_expression_gen
}
[@@deriving eq,ord,show]

type raw_function = (string * ptype option) raw_function_gen
[@@deriving eq,ord,show]

type 'a raw_program_gen = 'a raw_function_gen list
[@@deriving eq,ord,show]

type raw_program = (string * ptype option) raw_program_gen
[@@deriving eq,ord,show]

let make_predicate p args = Pred (p, args)

let mk_int n  = AInt n
let mk_nondet_int () = ANonDet
let mk_bool b = Bool b
let mk_var x     = PVar (x, None)
let mk_op op as' = AOp(op, as')

let mk_nondet p1 p2 = PNonDet (p1, p2)

let mk_ands = function
  | [] -> Bool true
  | x::xs -> Core.List.fold_left xs ~init:x ~f:(fun a b -> And(a, b))

let mk_ors = function
  | [] -> Bool false
  | x::xs -> Core.List.fold_left xs ~init:x ~f:(fun a b -> Or(a, b))

(* let mk_not x = Not x *)

let mk_arg s t = (s, t)

let mk_pred pred a1 a2 = Pred(pred, [a1;a2])

let mk_app t1 t2 = PApp(t1, t2)
let mk_apps t ts = Core.List.fold_left ts ~init:t ~f:mk_app
let mk_if p t e = PIf (p, t, e)
let mk_event e p = PEvent (e, p)
let mk_lambda args body = PLambda (args, body)
let mk_let x expr1 expr2 = PLet (x, expr1, expr2)
