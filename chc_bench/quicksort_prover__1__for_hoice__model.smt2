(model
  (define-fun X83
    ((v_0 Int) (v_1 Int)) Bool
    (and
      (>= (+ v_1 v_0) 1)
      (>= (+ v_1 (* (- 1) v_0)) 1)
    )
  )
  (define-fun X82
    ((v_0 Int) (v_1 Int) (v_2 Int)) Bool
    (and
      (>= (+ v_1 v_2) 1)
      (>= (+ (* (- 1) v_1) v_2) 1)
    )
  )
  (define-fun X3
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int)) Bool
    (and
      (>= v_1 0)
      (>= v_2 0)
      (>= v_3 0)
      (>= (+ v_6 (* (- 1) v_1)) 1)
      (>= (+ v_5 (* (- 1) v_1) (* (- 1) v_2) (* (- 1) v_3)) 2)
    )
  )
  (define-fun X4
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int)) Bool
    (and
      (>= v_0 0)
      (>= v_1 0)
      (>= v_2 0)
      (>= (+ (* (- 1) v_0) v_5) 1)
      (>= (+ (* (- 1) v_0) (* (- 1) v_1) (* (- 1) v_2) v_4) 2)
    )
  )
  (define-fun X1
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int)) Bool true
  )
  (define-fun X6
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int)) Bool true
  )
  (define-fun X2
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int)) Bool
    (and
      (>= v_2 2)
      (>= v_3 1)
    )
  )
  (define-fun X170
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int)) Bool
    (and
      (>= v_2 0)
      (>= v_3 0)
      (>= (+ (* (- 1) v_1) v_6) 1)
      (>= (+ (* (- 1) v_1) (* (- 1) v_2) (* (- 1) v_3) v_5) 2)
      (>= v_1 1)
    )
  )
  (define-fun X169
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) (v_7 Int)) Bool
    (and
      (>= v_3 0)
      (>= v_4 0)
      (>= (+ (* (- 1) v_2) v_7) 1)
      (>= (+ (* (- 1) v_2) (* (- 1) v_3) (* (- 1) v_4) v_6) 2)
      (>= v_2 1)
    )
  )
  (define-fun X168
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) (v_7 Int) (v_8 Int) (v_9 Int) (v_10 Int) (v_11 Int) (v_12 Int)) Bool true
  )
  (define-fun X167
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) (v_7 Int) (v_8 Int) (v_9 Int) (v_10 Int) (v_11 Int)) Bool
    (and
      (>= v_1 1)
      (>= v_2 0)
      (>= (+ (* (- 1) v_0) v_11) 2)
      (>= (+ (* (- 1) v_0) (* (- 1) v_1) (* (- 1) (- 1)) (* v_2 (- 1)) v_10) 3)
      (>= v_0 0)
    )
  )
  (define-fun X166
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) (v_7 Int)) Bool
    (and
      (>= v_2 1)
      (>= v_3 0)
      (>= v_4 0)
      (>= (+ (* (- 1) v_2) v_7) 1)
      (>= (+ (* (- 1) v_2) (* (- 1) v_3) (* (- 1) v_4) v_6) 2)
    )
  )
  (define-fun X165
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) (v_7 Int) (v_8 Int) (v_9 Int) (v_10 Int) (v_11 Int) (v_12 Int)) Bool true
  )
  (define-fun X164
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) (v_7 Int) (v_8 Int) (v_9 Int) (v_10 Int) (v_11 Int)) Bool
    (and
      (>= v_0 0)
      (>= v_1 0)
      (>= v_2 1)
      (>= (+ (* (- 1) v_0) v_11) 2)
      (>= (+ (* (- 1) v_0) (* (- 1) v_1) (* (- 1) (+ (- 1) v_2)) v_10) 3)
    )
  )
  (define-fun X163
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int)) Bool
    (and
      (<= v_0 0)
      (>= v_0 0)
      (>= v_1 0)
      (>= v_2 0)
      (>= (+ (* (- 1) v_0) v_5) 1)
      (>= (+ (* (- 1) v_0) (* (- 1) v_1) (* v_2 (- 1)) v_4) 2)
    )
  )
  (define-fun X162
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int)) Bool
    (and
      (>= v_2 0)
      (>= v_6 1)
      (<= (+ (* (- 1) v_5) v_2) (- 2))
    )
  )
  (define-fun X161
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) (v_7 Int) (v_8 Int)) Bool true
  )
  (define-fun X160
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) (v_7 Int)) Bool
    (and
      (>= v_0 0)
      (>= v_7 1)
      (<= (+ (* (- 1) v_6) v_0) (- 2))
    )
  )
  (define-fun X159
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) (v_7 Int)) Bool true
  )
  (define-fun X158
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int)) Bool
    (and
      (= (+ (* (- 1) v_0) v_3) 0)
      (<= v_1 0)
      (>= v_1 0)
      (>= v_2 0)
      (>= v_3 0)
      (>= (+ (* (- 1) v_1) v_6) 1)
      (>= (+ (* (- 1) v_1) (* (- 1) v_2) (* v_3 (- 1)) v_5) 2)
    )
  )
  (define-fun X157
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int)) Bool
    (and
      (>= (+ v_0 (* (- 1) v_2)) 0)
      (>= (+ v_3 (* (- 1) v_2)) 1)
      (>= (+ v_0 (* (- 1) v_1)) 1)
      (>= v_2 1)
      (>= (+ v_1 v_0) 1)
    )
  )
  (define-fun X156
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) (v_7 Int) (v_8 Int)) Bool true
  )
  (define-fun X155
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) (v_7 Int)) Bool
    (and
      (= v_1 0)
      (= v_2 0)
      (>= (+ v_4 (* (- 1) v_0)) 1)
      (>= (+ v_7 (* (- 1) v_0)) 2)
      (>= (+ v_4 (* (- 1) v_3)) 1)
      (>= v_0 0)
      (>= (+ v_3 v_4) 1)
    )
  )
  (define-fun X154
    ((v_0 Int) (v_1 Int)) Bool
    (and
      (>= (+ v_1 v_0) 1)
      (>= (+ v_0 (* (- 1) v_1)) 1)
    )
  )
  (define-fun X153
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int)) Bool true
  )
  (define-fun X152
    ((v_0 Int) (v_1 Int) (v_2 Int)) Bool
    (and
      (= (+ (* (- 1) v_0) v_2) 0)
      (>= (+ v_2 v_1) 1)
      (>= (+ v_1 (* (- 1) v_2)) 1)
    )
  )
  (define-fun X5
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int)) Bool
    (and
      (>= v_3 2)
      (>= v_4 1)
    )
  )
  (define-fun X126
    ((v_0 Int) (v_1 Int)) Bool true
  )
  (define-fun X125
    ((v_0 Int)) Bool true
  )
  (define-fun X124
    () Bool true
  )
  (define-fun X94
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int)) Bool
    (and
      (>= v_2 1)
      (>= (+ v_3 (* (- 1) v_2)) 1)
    )
  )
  (define-fun X93
    ((v_0 Int) (v_1 Int) (v_2 Int)) Bool
    (and
      (>= (+ v_2 (* (- 1) v_1)) 1)
      (>= v_1 1)
    )
  )
  (define-fun X86
    ((v_0 Int) (v_1 Int) (v_2 Int)) Bool true
  )
  (define-fun X85
    ((v_0 Int) (v_1 Int) (v_2 Int)) Bool
    (>= v_2 2)
  )
  (define-fun X7
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int)) Bool true
  )
  (define-fun X81
    ((v_0 Int) (v_1 Int) (v_2 Int)) Bool
    (>= v_2 2)
  )
  (define-fun X80
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int)) Bool true
  )
  (define-fun X14
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int)) Bool
    (and
      (>= v_2 0)
      (>= v_3 0)
      (>= (+ (* (- 1) v_1) v_6) 1)
      (>= (+ (* (- 1) v_1) (* (- 1) v_2) (* (- 1) v_3) v_5) 2)
      (>= v_1 1)
    )
  )
  (define-fun X136
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int)) Bool true
  )
  (define-fun X84
    ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int)) Bool
    (>= v_3 2)
  )
)