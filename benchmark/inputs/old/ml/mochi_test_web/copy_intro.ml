let rec copy x = if x=0 then 0 else 1 + copy (x-1)
let main n = assert (copy (copy n) = n)
