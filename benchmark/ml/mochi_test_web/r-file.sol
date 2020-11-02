sat
(model
  (define-fun |fail_64[0:0]|
    ( (v_0 Int) ) Bool
    false
  )
  (define-fun |g[0:2]|
    ( (v_0 Int) (v_1 Bool) (v_2 Int) ) Bool
    (and v_1 (= (+ (- 1) v_2) 0))
  )
  (define-fun |f[0:2]|
    ( (v_0 Bool) (v_1 Bool) (v_2 Int) ) Bool
    (and (= (+ (- 3) v_2) 0) v_1 v_0)
  )
  (define-fun |read_[0:1]|
    ( (v_0 Bool) (v_1 Int) ) Bool
    (or (not v_0) (= (+ v_1 (- 1)) 0) (= (+ v_1 (- 3)) 0))
  )
  (define-fun |read_[0:2][0:0]|
    ( (v_0 Bool) (v_1 Int) (v_2 Int) ) Bool
    (and (not v_0) (= (+ (* (- 1) v_1) v_2) 0) (|read_[0:1]| false v_2))
  )
)
