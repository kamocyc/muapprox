sat
(model
  (define-fun |replicate[0:2][0:0]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) ) Bool
    true
  )
  (define-fun |replicate[0:2][0:1][0:1][0:0]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) ) Bool
    (= (+ v_4 (* (- 1) v_0)) 0)
  )
  (define-fun |fail_65[0:0]|
    ( (v_0 Int) ) Bool
    false
  )
  (define-fun |replicate[0:1]|
    ( (v_0 Int) (v_1 Int) ) Bool
    true
  )
  (define-fun |all_equal[0:1]|
    ( (v_0 Int) (v_1 Int) ) Bool
    (exists ( (v_2 Int) ) (|replicate[0:2][0:0]| v_0 v_2 v_1))
  )
  (define-fun |all_equal[0:2][0:1][0:0]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) ) Bool
    (or (>= (* (- 1) v_1) 0) (= (+ v_0 (* (- 1) v_3)) 0) (not (= v_2 0)) (not (|all_equal[0:1]| v_0 v_1)))
  )
)
