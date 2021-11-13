; POPL13の例
; これはz3で解ける
; (declare-const p1 Int)
; (declare-const p2 Int)
; (declare-const p4 Int)


  (define-fun p2 () Int
    (- 1))
  (define-fun p4 () Int
    (- 1))
  (define-fun p1 () Int
    0)
    
; (assert
;   (forall
;     ((x Int) (y Int) (z Int))
;     (=>
;       (and
;         (= (* p4 x) (* p4 z))
;         (= 0 (* (+ (* p1 p4) p2) (+ (- z y) 1)))
;       )
;       (<= x y)
;     )
;   )
; )

(assert
  (forall
    ((x Int) (y Int) (z Int))
    (=>
      (and
        (= (* p4 x) (* p4 z))
        (= (+ (* p1 p4 x) (* p2 z)) (* (+ (* p1 p4) p2) (- y 1)))
      )
      (<= x y)
    )
  )
)

(check-sat)
(get-model)

; p1 = 0
; p2 = -1
; p4 = 1

; x = z /\ z = y - 1 => x <= y
; x = y - 1
