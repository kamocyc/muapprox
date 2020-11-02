sat
(model
  (define-fun |length[0:2][0:0]|
    ( (v_0 Int) (v_1 Int) ) Bool
    (or (= (+ v_0 (* (- 1) v_1)) 0) (and (>= (* (- 1) v_1) 0) (not (= (+ v_0 (* (- 1) v_1)) 0)) (>= (* (- 1) v_0) 1)))
  )
  (define-fun |make_int_list_23[0:1][0:0]|
    ( (v_0 Int) (v_1 Int) ) Bool
    true
  )
  (define-fun |make_int_list[0:2][0:0]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) ) Bool
    true
  )
  (define-fun |length[0:0]|
    ( (v_0 Int) ) Bool
    true
  )
  (define-fun |fail_195[0:0]|
    ( (v_0 Int) ) Bool
    false
  )
  (define-fun |make_int_list_23[0:0]|
    ( (v_0 Int) ) Bool
    true
  )
  (define-fun |make_int_list[0:1]|
    ( (v_0 Int) (v_1 Int) ) Bool
    (|make_int_list_23[0:1][0:0]| 0 v_0)
  )
  (define-fun |combine[0:2]|
    ( (v_0 Int) (v_1 Int) ) Bool
    (exists ( (v_2 Int) ) (and (|make_int_list[0:2][0:0]| v_0 0 v_1) (|length[0:2][0:0]| v_1 v_2) (|length[0:2][0:0]| v_0 v_2) (|make_int_list_23[0:1][0:0]| 0 v_0)))
  )
)
