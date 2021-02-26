let f1 (u:unit) (c:unit->unit) (d:unit) = d
let f2 (u:unit) (a:((unit->unit)->unit->unit)->unit->unit) (b:unit->unit) = a (f1 u)
let f3 (u:unit) (a:((unit->unit)->unit->unit)->unit->unit) = a (f2 u a)
let f4 (u:unit) (v:unit) = v
let f5 (u:unit) (e:(unit->unit)->(unit->unit)) = e (f4 u)
let main (u:unit) =
  let zz_1032 = f3 u (f5 u) in ()
