sat
(model
  (define-fun |map[0:2][0:1][0:0]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) ) Bool
    (>= v_2 1)
  )
  (define-fun |clone_38[0:3]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) ) Bool
    true
  )
  (define-fun |clone_38[0:4][0:0]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) ) Bool
    (or (and (>= (* (- 1) v_3) 0) (>= v_4 0)) (and (>= v_4 1) (>= v_3 1)))
  )
  (define-fun |clone[0:4]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) ) Bool
    true
  )
  (define-fun |clone[0:5][0:0]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) ) Bool
    true
  )
  (define-fun |map[0:1]|
    ( (v_0 Int) ) Bool
    true
  )
  (define-fun |fail_140[0:0]|
    ( (v_0 Int) ) Bool
    false
  )
  (define-fun |clone[0:5][0:1][0:1][0:0]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) ) Bool
    (and (= (+ v_6 (* (- 1) v_2)) 0) (= v_5 0) (>= v_3 1) (|clone[0:4]| v_0 v_1 v_6 v_3) (|clone[0:5][0:0]| v_0 v_1 v_6 v_3 v_4) (|clone[0:5][0:0]| v_0 v_1 v_6 (+ v_3 (- 1)) (+ v_4 (- 1))))
  )
  (define-fun |clone_38[0:4][0:1][0:1][0:0]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) ) Bool
    (and (= v_5 0) (>= v_3 1) (|clone_38[0:4][0:0]| v_0 v_1 0 (+ v_3 (- 1)) (+ v_4 (- 1))) (|clone_38[0:4][0:0]| v_0 v_1 v_2 v_3 v_4) (|clone_38[0:3]| v_0 v_1 v_2 v_3))
  )
  (define-fun |clone[0:3][0:1][0:0]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) ) Bool
    (and (= v_1 0) (|clone_38[0:4][0:0]| v_0 0 0 v_0 v_2) (|clone_38[0:4][0:1][0:1][0:0]| v_0 0 0 v_0 v_2 v_3 0))
  )
  (define-fun |clone[0:5][0:1][0:1][0:1][0:1][0:0]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) (v_7 Int) (v_8 Int) ) Bool
    (and (= (+ v_6 (* (- 1) v_2)) 0) (= v_5 0) (>= v_3 1) (|clone[0:5][0:1][0:1][0:0]| v_0 v_1 v_6 v_3 v_4 0 v_6) (|clone[0:5][0:0]| v_0 v_1 v_6 v_3 v_4) (|clone[0:5][0:0]| v_0 v_1 v_6 (+ v_3 (- 1)) (+ v_4 (- 1))) (|clone[0:4]| v_0 v_1 v_6 v_3) (|clone[0:3][0:1][0:0]| v_0 v_1 v_6 v_7 0))
  )
  (define-fun |map[0:0][0:0]|
    ( (v_0 Int) ) Bool
    (exists ( (v_1 Int) ) (and (>= v_1 1) (|map[0:2][0:1][0:0]| v_1 0 v_0) (|map[0:1]| v_1)))
  )
  (define-fun |map[0:0][0:1][0:1][0:0]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) ) Bool
    (exists ( (v_4 Int) (v_3 Int) ) (and (>= v_3 1) (>= v_4 1) (= v_1 0) (|map[0:2][0:1][0:0]| v_3 0 v_0) (|map[0:1]| v_3) (|clone[0:5][0:0]| v_4 0 v_0 v_4 v_3) (|clone[0:5][0:0]| v_4 0 v_0 (+ v_4 (- 1)) (+ v_3 (- 1))) (|clone[0:4]| v_4 0 v_0 v_4) (|map[0:0][0:0]| v_0) (|clone_38[0:4][0:0]| v_4 0 0 v_4 v_0) (|clone_38[0:4][0:0]| v_4 0 0 (+ v_4 (- 1)) (+ v_0 (- 1))) (|clone_38[0:3]| v_4 0 0 v_4)))
  )
  (define-fun |map[0:2][0:1][0:1][0:1][0:0]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) ) Bool
    (or (>= (* (- 1) v_0) 0) (not (= v_1 0)) (|map[0:0][0:1][0:1][0:0]| v_2 v_3 0) (not (|map[0:2][0:1][0:0]| v_0 0 v_2)) (not (|map[0:0][0:0]| v_2)) (not (|map[0:1]| v_0)))
  )
  (define-fun |map[0:0][0:2][0:0]|
    ( (v_0 Int) (v_1 Int) ) Bool
    (exists ( (v_4 Int) (v_2 Int) (v_3 Int) ) (and (>= v_0 1) (|map[0:0][0:1][0:1][0:0]| v_0 0 0) (|clone[0:5][0:0]| v_2 0 v_3 v_2 v_4) (|map[0:0][0:0]| v_0) (|clone_38[0:4][0:0]| v_2 0 0 v_2 v_3)))
  )
)
