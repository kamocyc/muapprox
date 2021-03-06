sat
(model
  (define-fun |length[0:2][0:0]|
    ( (v_0 Int) (v_1 Int) ) Bool
    (or (= v_1 0) (and (>= v_0 1) (not (= v_1 0))))
  )
  (define-fun |length[0:0]|
    ( (v_0 Int) ) Bool
    true
  )
  (define-fun |fail_169[0:0]|
    ( (v_0 Int) ) Bool
    false
  )
  (define-fun |make_int_list[0:1]|
    ( (v_0 Int) (v_1 Int) ) Bool
    true
  )
  (define-fun |make_int_list[0:2][0:0]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) ) Bool
    (= v_2 0)
  )
  (define-fun |divide[0:1]|
    ( (v_0 Int) (v_1 Int) ) Bool
    (|make_int_list[0:2][0:0]| v_0 0 v_1)
  )
  (define-fun |divide[0:3][0:2]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) ) Bool
    (and (>= (* (- 1) v_1) 0) (= v_3 0) (= v_2 0) (|divide[0:1]| v_0 v_1))
  )
)
