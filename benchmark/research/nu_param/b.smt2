; a.smt2を作るもとの式
; 直接z3では解けない
; recusionが無いので、simpleなアルゴリズムでa.smt2に可能
(declare-fun P1 (Int) Bool)
(declare-fun P2 (Int Int) Bool)
(declare-fun P3 (Int Int) Bool)
(declare-fun P4 (Int) Bool)
(declare-fun P5 (Int Int) Bool)
(declare-fun P6 (Int Int) Bool)
(declare-fun P7 (Int) Bool)
(declare-fun P8 (Int Int) Bool)

(declare-const p0 Int)
(declare-const p1 Int)
(declare-const p2 Int)
(declare-const p3 Int)
(declare-const p4 Int)

(assert (forall ((a Int) (x Int)) (=> (and (P1 a) (P3 a x)) (P4 (+ p0 (* p1 a) (* p2 x))))))
(assert (forall ((a Int) (x Int) (u Int)) (=> (and (P1 a) (P3 a x) (P5 (+ p0 (* p1 a) (* p2 x)) u)) (P2 a u))))
(assert (forall ((a Int) (x Int)) (=> (and (P1 a) (P3 a x)) (P6 (+ p0 (* p1 a) (* p2 x)) (+ x 1)))))
(assert (forall ((a Int) (x Int) (u Int)) (=> (and (P4 a) (P6 a x)) (P5 a x))))
(assert (forall ((x Int) (y Int)) (=> (and (P7 x) (P8 x y)) (<= x y))))
(assert (forall ((i Int)) (=> true (P1 (+ p3 (* p4 i))))))
(assert (forall ((i Int) (u Int)) (=> (P2 (+ p3 (* p4 i)) u) (P8 i u))))
(assert (forall ((i Int)) (=> true (P7 i))))
(assert (forall ((i Int)) (=> true (P3 (+ p3 (* p4 i)) i))))

(check-sat)
(get-model)
