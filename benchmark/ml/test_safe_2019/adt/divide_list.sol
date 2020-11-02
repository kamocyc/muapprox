sat
(model
  (define-fun |length[0:2][0:0]|
    ( (v_0 Int) (v_1 Int) ) Bool
    (= v_1 0)
  )
  (define-fun |make_int_list[0:1][0:0]|
    ( (v_0 Int) (v_1 Int) ) Bool
    true
  )
  (define-fun |fail_234[0:0]|
    ( (v_0 Int) ) Bool
    false
  )
  (define-fun |make_int_list[0:0]|
    ( (v_0 Int) ) Bool
    true
  )
  (define-fun |divide[0:0]|
    ( (v_0 Int) ) Bool
    (exists ( (v_1 Int) ) (|make_int_list[0:1][0:0]| 0 v_0))
  )
  (define-fun |divide[0:2][0:2]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) ) Bool
    (and (= v_1 0) (>= (* (- 1) v_0) 0) (|divide[0:0]| v_0))
  )
  (define-fun |make_int_list[0:1][0:1][0:1][0:0]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) ) Bool
    true
  )
  (define-fun |length[0:0]|
    ( (v_0 Int) ) Bool
    (or (>= v_0 1) (|length[0:2][0:0]| v_0 0))
  )
  (define-fun |length[0:1][0:1][0:0]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) ) Bool
    (exists ( (v_3 Int) ) (and (>= (* (- 1) v_0) 0) (|length[0:0]| v_0) (|make_int_list[0:1][0:1][0:1][0:0]| v_3 v_0 v_1 0) (|divide[0:0]| v_0) (|make_int_list[0:1][0:0]| 0 v_0)))
  )
)
