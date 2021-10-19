let const x () = x
let rec finish() = event "A"; finish()
let rec f g = let n = g() in if n>0 then f (const (n-1)) else finish()
let main = let n = Random.int(0) in f (const n)

(*{SPEC}
  fairness: (A, Never)
{SPEC}*)
