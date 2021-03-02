open Hflmc2_syntax
open Common_type
  
type raw_program =
    PUnit
  | PVar of string
  | PIf of raw_program * raw_program * raw_program
  | PEvent of program_event * raw_program
  | PNonDet of raw_program * raw_program
  | PApp of raw_program * raw_program
  | AInt of int
  | AOp of arith_op * raw_program list
  | Pred of pred_op * raw_program list 
  | And of raw_program * raw_program
  | Or of raw_program * raw_program
  | Bool of bool
  [@@deriving eq,ord,show]

type func = {
  var: string;
  args: (string * Type.simple_argty) list;
  body: raw_program
}
[@@deriving eq,ord,show]

type hes = func list
[@@deriving eq,ord,show]

let make_predicate p args = Pred (p, args)

let mk_int n  = AInt n
let mk_bool b = Bool b
let mk_var x     = PVar x
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

