; (set-logic HORN)
(declare-fun X1 (Int Int) Bool)
(declare-fun X2 (Int Int) Bool)
(declare-fun X3 (Int Int) Bool)
(declare-fun X4 (Int Int) Bool)
(declare-fun X7 (Int Int) Bool)
(declare-fun X31 () Bool)
(declare-fun X32 (Int) Bool)
(declare-fun X33 (Int Int) Bool)
(declare-fun X43 (Int Int Int) Bool)
(declare-fun X44 (Int Int Int) Bool)

; これで解けるはずだが解けない
(define-fun X3 ((x1 Int) (x2 Int)) Bool
  (or
    (and (>= (- (- x1 x2) 1) 0) (>= (- (+ 1 x2) x1) 0))
    (and (>= (+ 2 (* 3 x1)) 0) (>= (- (- 0 2) x1) 0))
  ))

(define-fun X7 ((x1 Int) (x2 Int)) Bool
  (or
    (and (< x2 0) (>= (- (- x2 1) x1) 0) (>= (- (+ x1 x2) 1) 0) (>= (+ 1 (* 2 x2)) 0))
    (and (>= x2 0) (>= (- (+ x1 x2) 1) 0) (>= (+ x1 x2) 0) (>= (+ (- 1 x1) x2) 0))
  ))

X3(x1: int, x2: int) :=
  -1 + x1 + -x2 >= 0 /\ 1 + -x1 + x2 >= 0 \/ 2 + 3 * x1 >= 0 /\ -2 + -x1 >= 0
X7(x1: int, x2: int) :=
  x2 < 0 /\ -1 + -x1 + x2 >= 0 /\ -1 + x1 + x2 >= 0 /\ 1 + 2 * x2 >= 0 \/ x2 >= 0 /\ -1 + x1 + x2 >= 0 /\ x1 + x2 >= 0 /\ 1 + -x1 + x2 >= 0

(assert (forall ((x48 Int)(x49 Int)) (=> (and (X1  x49 x48) (not (=  x48 x49))) false)))
(assert (forall ((x45 Int)(x47 Int)) (=> (X3  x47 x45) (X4  x47 x45))))
(assert (forall ((x34 Int)(x45 Int)(x46 Int)) (=> (and (X3  x34 x45) (X4  x46 x45)) (X2  x46 x45))))
(assert (forall ((tmp50 Int)(tmp51 Int)(tmp52 Int)(x43 Int)(x44 Int)) (=> (and (and (and (=  tmp50 (-  x43 1)) (=  tmp51 x44)) (=  tmp52 x44)) (X7  x44 x43)) (or (or (X7  x44 tmp50) (X44  x44 tmp51 x43)) (X43  x44 tmp52 x43)))))
(assert (forall ((x43 Int)(x44 Int)) (=> (and (X7  x44 x43) (<  x43 0)) false)))
(assert (forall ((e6 Int)(n7 Int)(tmp53 Int)(x42 Int)) (=> (and (=  tmp53 (-  0 e6)) (X44  x42 n7 e6)) (X3  x42 tmp53))))
(assert (forall ((e6 Int)(n7 Int)(x34 Int)(x41 Int)) (=> (and (X44  x34 n7 e6) (X2  x41 (-  0 e6))) (X1  x41 n7))))
(assert (forall ((e6 Int)(n7 Int)(x40 Int)) (=> (X43  x40 n7 e6) (X3  x40 e6))))
(assert (forall ((e6 Int)(n7 Int)(x34 Int)(x39 Int)) (=> (and (X43  x34 n7 e6) (X2  x39 e6)) (X1  x39 n7))))
(assert (forall ((n4 Int)) (=> X31 (X32  n4))))
(assert (forall ((e5 Int)(n4 Int)) (=> (X32  n4) (X33  e5 n4))))
(assert (forall ((e5 Int)(n4 Int)) (=> (and (X33  e5 n4) (and (and (>=  e5 1) (>=  e5 (+  1 (*  (-  0 1) n4)))) (>=  e5 (+  1 (*  1 n4))))) (X7  n4 e5))))
(assert (=> true X31))
; (assert (forall () (=> true X31)))
(check-sat)
(get-model)
