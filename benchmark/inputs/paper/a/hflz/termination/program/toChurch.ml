let compose (f : int -> int) (g : int -> int) x = f (g x)
let id (x : int) = x
let succ x = x + 1
let rec toChurch n f =
  if n = 0 then id else compose f (toChurch (n - 1) f)
let main () =
  let x = Random.int 0 in
  if x>=0 then
    let tos = toChurch x succ in
    let dummy__1 = Random.int 0 in tos dummy__1
  else 0
