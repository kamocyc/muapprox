open Hflmc2_syntax

type 'a id = 'a Id.t
[@@deriving eq,ord,show]
type arith_op = Arith.op
[@@deriving eq,ord,show]
type pred_op = Formula.pred
[@@deriving eq,ord,show]
type program_event = string
[@@deriving eq,ord,show]