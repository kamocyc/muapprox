sat
(model
  (define-fun |fail_110[0:0]|
    ( (v_0 Int) ) Bool
    false
  )
  (define-fun |make_unit_list[0:0]|
    ( (v_0 Int) ) Bool
    true
  )
  (define-fun |make_unit_list[0:1][0:0]|
    ( (v_0 Int) (v_1 Int) ) Bool
    true
  )
  (define-fun |combine[0:2]|
    ( (v_0 Int) (v_1 Int) ) Bool
    (and (= (+ v_0 (* (- 1) v_1)) 0) (|make_unit_list[0:1][0:0]| 0 v_1))
  )
)
