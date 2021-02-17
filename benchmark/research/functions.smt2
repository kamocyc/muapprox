(define-fun imply ((p1 Bool)(p2 Bool)) Bool (or (not p1) p2))

(assert (=(imply false false)true))
(assert (=(imply false true)true))
(assert (=(imply true false)false))
(assert (=(imply true true)false))

(check-sat)
