open Hflmc2_util
type t = Least | Greatest
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let flip_fixpoint = function
  | Greatest -> Least
  | Least -> Greatest