sat
(model
  (define-fun |length[0:2][0:0]|
    ( (v_0 Int) (v_1 Int) ) Bool
    (or (= (+ v_0 (* (- 1) v_1)) 0) (and (not (= (+ v_0 (* (- 1) v_1)) 0)) (>= (* (- 1) v_0) 1)))
  )
  (define-fun |make_abst_option_list[0:1][0:0]|
    ( (v_0 Int) (v_1 Int) ) Bool
    true
  )
  (define-fun |length[0:0]|
    ( (v_0 Int) ) Bool
    true
  )
  (define-fun |fail_153[0:0]|
    ( (v_0 Int) ) Bool
    false
  )
  (define-fun |make_abst_option_list[0:0]|
    ( (v_0 Int) ) Bool
    true
  )
  (define-fun |length_27[0:0]|
    ( (v_0 Int) ) Bool
    (|make_abst_option_list[0:1][0:0]| 0 v_0)
  )
  (define-fun |length_27[0:2][0:0]|
    ( (v_0 Int) (v_1 Int) ) Bool
    (and (>= (* (- 1) v_0) 0) (= v_1 0) (|length_27[0:0]| v_0))
  )
  (define-fun |cat_maybes[0:0]|
    ( (v_0 Int) ) Bool
    (and (>= (* (- 1) v_0) 0) (|length_27[0:0]| v_0) (|make_abst_option_list[0:1][0:0]| 0 v_0))
  )
  (define-fun |cat_maybes[0:2][0:0]|
    ( (v_0 Int) (v_1 Int) ) Bool
    (and (>= (* (- 1) v_0) 0) (= v_1 0) (|make_abst_option_list[0:1][0:0]| 0 v_0))
  )
  (define-fun |cat_maybes[0:1][0:1][0:1]|
    ( (v_0 Int) (v_1 Int) (v_2 Bool) (v_3 Int) ) Bool
    (and (>= (* (- 1) v_0) 0) (= v_1 0) v_2 (|length_27[0:0]| v_0) (|make_abst_option_list[0:1][0:0]| 0 v_0) (|make_abst_option_list[0:1][0:0]| 0 (+ v_0 (- 1))) (|cat_maybes[0:0]| v_0))
  )
  (define-fun |make_abst_option_list[0:1][0:1][0:1][0:1]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Bool) (v_4 Int) ) Bool
    (or (>= v_1 1) (|cat_maybes[0:1][0:1][0:1]| v_1 v_2 v_3 0) (not (|length_27[0:0]| v_1)) (not (|make_abst_option_list[0:1][0:0]| 0 v_1)) (not (|cat_maybes[0:0]| v_1)))
  )
)
