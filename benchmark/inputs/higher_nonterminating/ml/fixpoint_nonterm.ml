let rec fix (f:int -> int) (n:int) =
  let n2 = f n in
  if n2 = n then n else fix f n2
let to_zero n =
  if n = 0 then 0
  else n - 1
let main () =
  let r = read_int () in
  if r <= (-3) then
    fix to_zero (-3)
  else if r <= 0 then
    fix to_zero 0
  else if r <= 1 then
    fix to_zero 1
  else if r <= 3 then
    fix to_zero 3
  else
    fix to_zero 10
