sat
(model
  (define-fun |make_int_list[0:1][0:0]|
    ( (v_0 Int) (v_1 Int) ) Bool
    true
  )
  (define-fun |length[0:0]|
    ( (v_0 Int) ) Bool
    true
  )
  (define-fun |length[0:2][0:0]|
    ( (v_0 Int) (v_1 Int) ) Bool
    (or (= (+ v_0 (* (- 1) v_1)) 0) (and (not (= (+ v_0 (* (- 1) v_1)) 0)) (not (= v_0 0))))
  )
  (define-fun |fail_102[0:0]|
    ( (v_0 Int) ) Bool
    false
  )
  (define-fun |make_int_list[0:0]|
    ( (v_0 Int) ) Bool
    true
  )
  (define-fun |filter_acc[0:3]|
    ( (v_0 Int) (v_1 Int) ) Bool
    (and (= v_0 0) (|make_int_list[0:1][0:0]| 0 v_1))
  )
  (define-fun |filter_acc[0:5][0:0]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) ) Bool
    (and (= v_2 0) (>= (* (- 1) v_1) 0) (= v_0 0) (|make_int_list[0:1][0:0]| 0 v_1))
  )
  (define-fun |filter_acc[0:0][0:1][0:0]|
    ( (v_0 Int) (v_1 Bool) ) Bool
    (exists ( (v_2 Int) ) (and (not v_1) (|make_int_list[0:1][0:0]| 0 v_2)))
  )
  (define-fun |filter_acc[0:4][0:1][0:0]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) ) Bool
    (and (= v_2 0) (= v_0 0) (|make_int_list[0:1][0:0]| 0 (+ v_1 (- 1))) (|make_int_list[0:1][0:0]| 0 v_1) (|filter_acc[0:3]| 0 v_1))
  )
  (define-fun |make_int_list[0:1][0:1][0:1][0:0]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) ) Bool
    (or (|filter_acc[0:4][0:1][0:0]| 0 v_1 v_2 0) (not (|make_int_list[0:1][0:0]| 0 v_1)) (not (|filter_acc[0:3]| 0 v_1)))
  )
)
