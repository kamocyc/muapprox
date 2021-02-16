; CHC for hoice
; Hoice will time-out. However, a solution should be representable by hoice.
; This CHC is obtained from a quicksort termination benchmark.
(set-logic HORN)
(declare-fun X1 (Int Int Int Int Int) Bool)
(declare-fun X2 (Int Int Int Int) Bool)
(declare-fun X3 (Int Int Int Int Int Int Int) Bool)
(declare-fun X4 (Int Int Int Int Int Int) Bool)
(declare-fun X5 (Int Int Int Int Int) Bool)
(declare-fun X6 (Int Int Int Int) Bool)
(declare-fun X7 (Int Int Int Int Int Int Int) Bool)
(declare-fun X14 (Int Int Int Int Int Int Int) Bool)
(declare-fun X80 (Int Int Int Int) Bool)
(declare-fun X81 (Int Int Int) Bool)
(declare-fun X82 (Int Int Int) Bool)
(declare-fun X83 (Int Int) Bool)
(declare-fun X84 (Int Int Int Int) Bool)
(declare-fun X85 (Int Int Int) Bool)
(declare-fun X86 (Int Int Int) Bool)
(declare-fun X93 (Int Int Int) Bool)
(declare-fun X94 (Int Int Int Int) Bool)
(declare-fun X124 () Bool)
(declare-fun X125 (Int) Bool)
(declare-fun X126 (Int Int) Bool)
(declare-fun X136 (Int Int Int Int Int) Bool)
(declare-fun X152 (Int Int Int) Bool)
(declare-fun X153 (Int Int Int Int) Bool)
(declare-fun X154 (Int Int) Bool)
(declare-fun X155 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun X156 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun X157 (Int Int Int Int) Bool)
(declare-fun X158 (Int Int Int Int Int Int Int) Bool)
(declare-fun X159 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun X160 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun X161 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun X162 (Int Int Int Int Int Int Int) Bool)
(declare-fun X163 (Int Int Int Int Int Int) Bool)
(declare-fun X164 (Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun X165 (Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun X166 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun X167 (Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun X168 (Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun X169 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun X170 (Int Int Int Int Int Int Int) Bool)
(assert
  (forall ((x218 Int) (x219 Int) (x223 Int) (x224 Int) (x225 Int) (x226 Int))
    (=>
      (and
        (X4 x226 x225 x224 x223 x219 x218)
        (<= x218 0)
      )
      false
    )
  )
)
(assert
  (forall ((x218 Int) (x219 Int) (x223 Int) (x224 Int) (x225 Int) (x226 Int))
    (=>
      (and
        (X4 x226 x225 x224 x223 x219 x218)
        (<= x226 0)
      )
      (X163 x226 x225 x224 x223 x219 x218)
    )
  )
)
(assert
  (forall ((m23 Int) (x218 Int) (x219 Int) (x223 Int) (x224 Int) (x225 Int) (x226 Int))
    (=>
      (and
        (X4 x226 x225 x224 x223 x219 x218)
        (> x226 0)
      )
      (X14 m23 x226 x225 x224 x223 x219 x218)
    )
  )
)
(assert
  (forall ((x218 Int) (x219 Int) (x223 Int) (x224 Int) (x225 Int) (x226 Int) (x227 Int))
    (=>
      (and
        (X4 x226 x225 x224 x223 x219 x218)
        (X7 x227 x226 x225 x224 x223 x219 x218)
      )
      (X3 x227 x226 x225 x224 x223 x219 x218)
    )
  )
)
(assert
  (forall ((l82 Int) (r83 Int) (x81 Int) (x218 Int) (x219 Int) (x220 Int) (x221 Int) (xs84 Int))
    (=>
      (and
        (X4 xs84 r83 l82 x81 x219 x218)
        (X6 x221 x220 x219 x218)
      )
      (X2 x221 x220 x219 x218)
    )
  )
)
(assert
  (forall ((l82 Int) (r83 Int) (x81 Int) (x218 Int) (x219 Int) (x220 Int) (x221 Int) (x222 Int) (xs84 Int))
    (=>
      (and
        (and
          (X4 xs84 r83 l82 x81 x219 x218)
          (X6 x221 x220 x219 x218)
        )
        (X1 x222 x221 x220 x219 x218)
      )
      (X5 x222 x221 x220 x219 x218)
    )
  )
)
(assert
  (forall ((l17 Int) (m23 Int) (r18 Int) (recPar18413 Int) (recQs18314 Int) (x16 Int) (xs19 Int))
    (=>
      (X14 m23 xs19 r18 l17 x16 recQs18314 recPar18413)
      (X170 m23 xs19 r18 l17 x16 recQs18314 recPar18413)
    )
  )
)
(assert
  (forall ((l17 Int) (m23 Int) (r18 Int) (recPar18413 Int) (recQs18314 Int) (x16 Int) (xs19 Int))
    (=>
      (X170 m23 xs19 r18 l17 x16 recQs18314 recPar18413)
      (X6 x16 m23 recQs18314 recPar18413)
    )
  )
)
(assert
  (forall ((l17 Int) (m23 Int) (r18 Int) (recPar18413 Int) (recQs18314 Int) (x16 Int) (x217 Int) (xs19 Int))
    (=>
      (and
        (and
          (X170 m23 xs19 r18 l17 x16 recQs18314 recPar18413)
          (X5 x217 x16 m23 recQs18314 recPar18413)
        )
        (= x217 1)
      )
      (X166 x217 m23 xs19 r18 l17 x16 recQs18314 recPar18413)
    )
  )
)
(assert
  (forall ((l17 Int) (m23 Int) (r18 Int) (recPar18413 Int) (recQs18314 Int) (x16 Int) (x217 Int) (xs19 Int))
    (=>
      (and
        (and
          (X170 m23 xs19 r18 l17 x16 recQs18314 recPar18413)
          (X5 x217 x16 m23 recQs18314 recPar18413)
        )
        (not
          (= x217 1)
        )
      )
      (X169 x217 m23 xs19 r18 l17 x16 recQs18314 recPar18413)
    )
  )
)
(assert
  (forall ((l17 Int) (m23 Int) (r18 Int) (r_ap_24 Int) (recPar18413 Int) (recQs18314 Int) (tmp228 Int) (tmp229 Int) (tmp230 Int) (tmp231 Int) (x16 Int) (xs19 Int))
    (=>
      (and
        (and
          (and
            (and
              (= tmp228 (- xs19 1))
              (= tmp229 (+ 1 r18))
            )
            (= tmp230 l17)
          )
          (= tmp231 x16)
        )
        (X169 r_ap_24 m23 xs19 r18 l17 x16 recQs18314 recPar18413)
      )
      (X167 tmp228 tmp229 l17 x16 r_ap_24 m23 xs19 r18 tmp230 tmp231 recQs18314 recPar18413)
    )
  )
)
(assert
  (forall ((l17 Int) (m23 Int) (r18 Int) (r_ap_24 Int) (recPar18413 Int) (recQs18314 Int) (x16 Int) (x216 Int) (xs19 Int))
    (=>
      (and
        (X169 r_ap_24 m23 xs19 r18 l17 x16 recQs18314 recPar18413)
        (X168 x216
          (- xs19 1)
          (+ 1 r18)
          l17 x16 r_ap_24 m23 xs19 r18 l17 x16 recQs18314 recPar18413
        )
      )
      (X7 x216 xs19 r18 l17 x16 recQs18314 recPar18413)
    )
  )
)
(assert
  (forall ((l17 Int) (m23 Int) (r18 Int) (r_ap_24 Int) (recPar18413 Int) (recQs18314 Int) (tmp232 Int) (x16 Int) (x211 Int) (x212 Int) (x213 Int) (x214 Int) (xs19 Int))
    (=>
      (and
        (= tmp232 (- recPar18413 1))
        (X167 x214 x213 x212 x211 r_ap_24 m23 xs19 r18 l17 x16 recQs18314 recPar18413)
      )
      (X4 x214 x213 x212 x211 recQs18314 tmp232)
    )
  )
)
(assert
  (forall ((l17 Int) (m23 Int) (r18 Int) (r_ap_24 Int) (recPar18413 Int) (recQs18314 Int) (x16 Int) (x211 Int) (x212 Int) (x213 Int) (x214 Int) (x215 Int) (xs19 Int))
    (=>
      (and
        (X167 x214 x213 x212 x211 r_ap_24 m23 xs19 r18 l17 x16 recQs18314 recPar18413)
        (X3 x215 x214 x213 x212 x211 recQs18314
          (- recPar18413 1)
        )
      )
      (X168 x215 x214 x213 x212 x211 r_ap_24 m23 xs19 r18 l17 x16 recQs18314 recPar18413)
    )
  )
)
(assert
  (forall ((l17 Int) (l82 Int) (m23 Int) (r18 Int) (r83 Int) (r_ap_24 Int) (recPar18413 Int) (recQs18314 Int) (x16 Int) (x81 Int) (x208 Int) (x209 Int) (xs19 Int) (xs84 Int))
    (=>
      (and
        (X167 xs84 r83 l82 x81 r_ap_24 m23 xs19 r18 l17 x16 recQs18314 recPar18413)
        (X2 x209 x208 recQs18314
          (- recPar18413 1)
        )
      )
      (X6 x209 x208 recQs18314 recPar18413)
    )
  )
)
(assert
  (forall ((l17 Int) (l82 Int) (m23 Int) (r18 Int) (r83 Int) (r_ap_24 Int) (recPar18413 Int) (recQs18314 Int) (tmp233 Int) (x16 Int) (x81 Int) (x208 Int) (x209 Int) (x210 Int) (xs19 Int) (xs84 Int))
    (=>
      (and
        (= tmp233 (- recPar18413 1))
        (and
          (and
            (X167 xs84 r83 l82 x81 r_ap_24 m23 xs19 r18 l17 x16 recQs18314 recPar18413)
            (X2 x209 x208 recQs18314
              (- recPar18413 1)
            )
          )
          (X5 x210 x209 x208 recQs18314 recPar18413)
        )
      )
      (X1 x210 x209 x208 recQs18314 tmp233)
    )
  )
)
(assert
  (forall ((l17 Int) (m23 Int) (r18 Int) (r_ap_24 Int) (recPar18413 Int) (recQs18314 Int) (tmp234 Int) (tmp235 Int) (tmp236 Int) (tmp237 Int) (x16 Int) (xs19 Int))
    (=>
      (and
        (and
          (and
            (and
              (= tmp234 (- xs19 1))
              (= tmp235 (+ 1 l17))
            )
            (= tmp236 r18)
          )
          (= tmp237 x16)
        )
        (X166 r_ap_24 m23 xs19 r18 l17 x16 recQs18314 recPar18413)
      )
      (X164 tmp234 r18 tmp235 x16 r_ap_24 m23 xs19 tmp236 l17 tmp237 recQs18314 recPar18413)
    )
  )
)
(assert
  (forall ((l17 Int) (m23 Int) (r18 Int) (r_ap_24 Int) (recPar18413 Int) (recQs18314 Int) (x16 Int) (x207 Int) (xs19 Int))
    (=>
      (and
        (X166 r_ap_24 m23 xs19 r18 l17 x16 recQs18314 recPar18413)
        (X165 x207
          (- xs19 1)
          r18
          (+ 1 l17)
          x16 r_ap_24 m23 xs19 r18 l17 x16 recQs18314 recPar18413
        )
      )
      (X7 x207 xs19 r18 l17 x16 recQs18314 recPar18413)
    )
  )
)
(assert
  (forall ((l17 Int) (m23 Int) (r18 Int) (r_ap_24 Int) (recPar18413 Int) (recQs18314 Int) (tmp238 Int) (x16 Int) (x202 Int) (x203 Int) (x204 Int) (x205 Int) (xs19 Int))
    (=>
      (and
        (= tmp238 (- recPar18413 1))
        (X164 x205 x204 x203 x202 r_ap_24 m23 xs19 r18 l17 x16 recQs18314 recPar18413)
      )
      (X4 x205 x204 x203 x202 recQs18314 tmp238)
    )
  )
)
(assert
  (forall ((l17 Int) (m23 Int) (r18 Int) (r_ap_24 Int) (recPar18413 Int) (recQs18314 Int) (x16 Int) (x202 Int) (x203 Int) (x204 Int) (x205 Int) (x206 Int) (xs19 Int))
    (=>
      (and
        (X164 x205 x204 x203 x202 r_ap_24 m23 xs19 r18 l17 x16 recQs18314 recPar18413)
        (X3 x206 x205 x204 x203 x202 recQs18314
          (- recPar18413 1)
        )
      )
      (X165 x206 x205 x204 x203 x202 r_ap_24 m23 xs19 r18 l17 x16 recQs18314 recPar18413)
    )
  )
)
(assert
  (forall ((l17 Int) (l82 Int) (m23 Int) (r18 Int) (r83 Int) (r_ap_24 Int) (recPar18413 Int) (recQs18314 Int) (x16 Int) (x81 Int) (x199 Int) (x200 Int) (xs19 Int) (xs84 Int))
    (=>
      (and
        (X164 xs84 r83 l82 x81 r_ap_24 m23 xs19 r18 l17 x16 recQs18314 recPar18413)
        (X2 x200 x199 recQs18314
          (- recPar18413 1)
        )
      )
      (X6 x200 x199 recQs18314 recPar18413)
    )
  )
)
(assert
  (forall ((l17 Int) (l82 Int) (m23 Int) (r18 Int) (r83 Int) (r_ap_24 Int) (recPar18413 Int) (recQs18314 Int) (tmp239 Int) (x16 Int) (x81 Int) (x199 Int) (x200 Int) (x201 Int) (xs19 Int) (xs84 Int))
    (=>
      (and
        (= tmp239 (- recPar18413 1))
        (and
          (and
            (X164 xs84 r83 l82 x81 r_ap_24 m23 xs19 r18 l17 x16 recQs18314 recPar18413)
            (X2 x200 x199 recQs18314
              (- recPar18413 1)
            )
          )
          (X5 x201 x200 x199 recQs18314 recPar18413)
        )
      )
      (X1 x201 x200 x199 recQs18314 tmp239)
    )
  )
)
(assert
  (forall ((l17 Int) (r18 Int) (recPar18413 Int) (recQs18314 Int) (tmp240 Int) (x16 Int) (xs19 Int))
    (=>
      (and
        (= tmp240 l17)
        (X163 xs19 r18 l17 x16 recQs18314 recPar18413)
      )
      (X158 l17 xs19 r18 tmp240 x16 recQs18314 recPar18413)
    )
  )
)
(assert
  (forall ((l17 Int) (r18 Int) (recPar18413 Int) (recQs18314 Int) (x16 Int) (x198 Int) (xs19 Int))
    (=>
      (and
        (X163 xs19 r18 l17 x16 recQs18314 recPar18413)
        (X159 x198 l17 xs19 r18 l17 x16 recQs18314 recPar18413)
      )
      (X162 x198 xs19 r18 l17 x16 recQs18314 recPar18413)
    )
  )
)
(assert
  (forall ((l17 Int) (r18 Int) (r_ap_21 Int) (recPar18413 Int) (recQs18314 Int) (tmp241 Int) (x16 Int) (xs19 Int))
    (=>
      (and
        (= tmp241 r18)
        (X162 r_ap_21 xs19 r18 l17 x16 recQs18314 recPar18413)
      )
      (X160 r18 r_ap_21 xs19 tmp241 l17 x16 recQs18314 recPar18413)
    )
  )
)
(assert
  (forall ((l17 Int) (r18 Int) (r_ap_21 Int) (recPar18413 Int) (recQs18314 Int) (tmp242 Int) (x16 Int) (x197 Int) (xs19 Int))
    (=>
      (and
        (= tmp242 (+ (+ r_ap_21 1) x197))
        (and
          (X162 r_ap_21 xs19 r18 l17 x16 recQs18314 recPar18413)
          (X161 x197 r18 r_ap_21 xs19 r18 l17 x16 recQs18314 recPar18413)
        )
      )
      (X7 tmp242 xs19 r18 l17 x16 recQs18314 recPar18413)
    )
  )
)
(assert
  (forall ((l17 Int) (r18 Int) (r_ap_21 Int) (recPar18413 Int) (recQs18314 Int) (tmp243 Int) (x16 Int) (x195 Int) (xs19 Int))
    (=>
      (and
        (= tmp243 (- recQs18314 1))
        (X160 x195 r_ap_21 xs19 r18 l17 x16 recQs18314 recPar18413)
      )
      (X83 x195 tmp243)
    )
  )
)
(assert
  (forall ((l17 Int) (r18 Int) (r_ap_21 Int) (recPar18413 Int) (recQs18314 Int) (x16 Int) (x195 Int) (x196 Int) (xs19 Int))
    (=>
      (and
        (X160 x195 r_ap_21 xs19 r18 l17 x16 recQs18314 recPar18413)
        (X82 x196 x195
          (- recQs18314 1)
        )
      )
      (X161 x196 x195 r_ap_21 xs19 r18 l17 x16 recQs18314 recPar18413)
    )
  )
)
(assert
  (forall ((l17 Int) (n47 Int) (r18 Int) (r_ap_21 Int) (recPar18413 Int) (recQs18314 Int) (x16 Int) (x192 Int) (x193 Int) (xs19 Int))
    (=>
      (and
        (X160 n47 r_ap_21 xs19 r18 l17 x16 recQs18314 recPar18413)
        (X81 x193 x192
          (- recQs18314 1)
        )
      )
      (X6 x193 x192 recQs18314 recPar18413)
    )
  )
)
(assert
  (forall ((l17 Int) (n47 Int) (r18 Int) (r_ap_21 Int) (recPar18413 Int) (recQs18314 Int) (tmp244 Int) (x16 Int) (x192 Int) (x193 Int) (x194 Int) (xs19 Int))
    (=>
      (and
        (= tmp244 (- recQs18314 1))
        (and
          (and
            (X160 n47 r_ap_21 xs19 r18 l17 x16 recQs18314 recPar18413)
            (X81 x193 x192
              (- recQs18314 1)
            )
          )
          (X5 x194 x193 x192 recQs18314 recPar18413)
        )
      )
      (X80 x194 x193 x192 tmp244)
    )
  )
)
(assert
  (forall ((l17 Int) (r18 Int) (recPar18413 Int) (recQs18314 Int) (tmp245 Int) (x16 Int) (x190 Int) (xs19 Int))
    (=>
      (and
        (= tmp245 (- recQs18314 1))
        (X158 x190 xs19 r18 l17 x16 recQs18314 recPar18413)
      )
      (X83 x190 tmp245)
    )
  )
)
(assert
  (forall ((l17 Int) (r18 Int) (recPar18413 Int) (recQs18314 Int) (x16 Int) (x190 Int) (x191 Int) (xs19 Int))
    (=>
      (and
        (X158 x190 xs19 r18 l17 x16 recQs18314 recPar18413)
        (X82 x191 x190
          (- recQs18314 1)
        )
      )
      (X159 x191 x190 xs19 r18 l17 x16 recQs18314 recPar18413)
    )
  )
)
(assert
  (forall ((l17 Int) (n47 Int) (r18 Int) (recPar18413 Int) (recQs18314 Int) (x16 Int) (x187 Int) (x188 Int) (xs19 Int))
    (=>
      (and
        (X158 n47 xs19 r18 l17 x16 recQs18314 recPar18413)
        (X81 x188 x187
          (- recQs18314 1)
        )
      )
      (X6 x188 x187 recQs18314 recPar18413)
    )
  )
)
(assert
  (forall ((l17 Int) (n47 Int) (r18 Int) (recPar18413 Int) (recQs18314 Int) (tmp246 Int) (x16 Int) (x187 Int) (x188 Int) (x189 Int) (xs19 Int))
    (=>
      (and
        (= tmp246 (- recQs18314 1))
        (and
          (and
            (X158 n47 xs19 r18 l17 x16 recQs18314 recPar18413)
            (X81 x188 x187
              (- recQs18314 1)
            )
          )
          (X5 x189 x188 x187 recQs18314 recPar18413)
        )
      )
      (X80 x189 x188 x187 tmp246)
    )
  )
)
(assert
  (forall ((x181 Int) (x185 Int))
    (=>
      (and
        (X83 x185 x181)
        (<= x181 0)
      )
      false
    )
  )
)
(assert
  (forall ((tmp247 Int) (x181 Int) (x185 Int))
    (=>
      (and
        (= tmp247 0)
        (and
          (X83 x185 x181)
          (<= x185 0)
        )
      )
      (X86 tmp247 x185 x181)
    )
  )
)
(assert
  (forall ((m11 Int) (x181 Int) (x185 Int))
    (=>
      (and
        (X83 x185 x181)
        (> x185 0)
      )
      (X93 m11 x185 x181)
    )
  )
)
(assert
  (forall ((x181 Int) (x185 Int) (x186 Int))
    (=>
      (and
        (X83 x185 x181)
        (X86 x186 x185 x181)
      )
      (X82 x186 x185 x181)
    )
  )
)
(assert
  (forall ((n47 Int) (x181 Int) (x182 Int) (x183 Int))
    (=>
      (and
        (X83 n47 x181)
        (X85 x183 x182 x181)
      )
      (X81 x183 x182 x181)
    )
  )
)
(assert
  (forall ((n47 Int) (x181 Int) (x182 Int) (x183 Int) (x184 Int))
    (=>
      (and
        (and
          (X83 n47 x181)
          (X85 x183 x182 x181)
        )
        (X80 x184 x183 x182 x181)
      )
      (X84 x184 x183 x182 x181)
    )
  )
)
(assert
  (forall ((m11 Int) (n9 Int) (recPar18412 Int) (recQs1837 Int))
    (=>
      (X93 m11 n9 recQs1837)
      (X94 recPar18412 m11 n9 recQs1837)
    )
  )
)
(assert
  (forall ((m11 Int) (n9 Int) (recPar18412 Int) (recQs1837 Int))
    (=>
      (and
        (X94 recPar18412 m11 n9 recQs1837)
        (and
          (and
            (and
              (and
                (>= recPar18412 1)
                (>= recPar18412 (+ 1 (* (- 0 1) m11)))
              )
              (>= recPar18412 (+ 1 (* 1 m11)))
            )
            (>= recPar18412 (+ 1 (* (- 0 1) (- n9 1))))
          )
          (>= recPar18412 (+ 1 (* 1 (- n9 1))))
        )
      )
      (X157 recPar18412 m11 n9 recQs1837)
    )
  )
)
(assert
  (forall ((m11 Int) (n9 Int) (recPar18412 Int) (recQs1837 Int) (tmp248 Int) (tmp249 Int) (tmp250 Int) (tmp251 Int))
    (=>
      (and
        (and
          (and
            (and
              (= tmp248 (- n9 1))
              (= tmp249 0)
            )
            (= tmp250 0)
          )
          (= tmp251 m11)
        )
        (X157 recPar18412 m11 n9 recQs1837)
      )
      (X155 tmp248 tmp249 tmp250 m11 recPar18412 tmp251 n9 recQs1837)
    )
  )
)
(assert
  (forall ((m11 Int) (n9 Int) (recPar18412 Int) (recQs1837 Int) (x180 Int))
    (=>
      (and
        (X157 recPar18412 m11 n9 recQs1837)
        (X156 x180
          (- n9 1)
          0 0 m11 recPar18412 m11 n9 recQs1837
        )
      )
      (X86 x180 n9 recQs1837)
    )
  )
)
(assert
  (forall ((m11 Int) (n9 Int) (recPar18412 Int) (recQs1837 Int) (x175 Int) (x176 Int) (x177 Int) (x178 Int))
    (=>
      (X155 x178 x177 x176 x175 recPar18412 m11 n9 recQs1837)
      (X4 x178 x177 x176 x175 recQs1837 recPar18412)
    )
  )
)
(assert
  (forall ((m11 Int) (n9 Int) (recPar18412 Int) (recQs1837 Int) (x175 Int) (x176 Int) (x177 Int) (x178 Int) (x179 Int))
    (=>
      (and
        (X155 x178 x177 x176 x175 recPar18412 m11 n9 recQs1837)
        (X3 x179 x178 x177 x176 x175 recQs1837 recPar18412)
      )
      (X156 x179 x178 x177 x176 x175 recPar18412 m11 n9 recQs1837)
    )
  )
)
(assert
  (forall ((l82 Int) (m11 Int) (n9 Int) (r83 Int) (recPar18412 Int) (recQs1837 Int) (x81 Int) (x172 Int) (x173 Int) (xs84 Int))
    (=>
      (and
        (X155 xs84 r83 l82 x81 recPar18412 m11 n9 recQs1837)
        (X2 x173 x172 recQs1837 recPar18412)
      )
      (X85 x173 x172 recQs1837)
    )
  )
)
(assert
  (forall ((l82 Int) (m11 Int) (n9 Int) (r83 Int) (recPar18412 Int) (recQs1837 Int) (x81 Int) (x172 Int) (x173 Int) (x174 Int) (xs84 Int))
    (=>
      (and
        (and
          (X155 xs84 r83 l82 x81 recPar18412 m11 n9 recQs1837)
          (X2 x173 x172 recQs1837 recPar18412)
        )
        (X84 x174 x173 x172 recQs1837)
      )
      (X1 x174 x173 x172 recQs1837 recPar18412)
    )
  )
)
(assert
  (forall ((n4 Int))
    (=> X124
      (X125 n4)
    )
  )
)
(assert
  (forall ((n4 Int) (recQs1835 Int))
    (=>
      (X125 n4)
      (X126 recQs1835 n4)
    )
  )
)
(assert
  (forall ((n4 Int) (recQs1835 Int))
    (=>
      (and
        (X126 recQs1835 n4)
        (and
          (and
            (>= recQs1835 1)
            (>= recQs1835 (+ 1 (* (- 0 1) n4)))
          )
          (>= recQs1835 (+ 1 (* 1 n4)))
        )
      )
      (X154 recQs1835 n4)
    )
  )
)
(assert
  (forall ((n4 Int) (recQs1835 Int) (tmp252 Int))
    (=>
      (and
        (= tmp252 n4)
        (X154 recQs1835 n4)
      )
      (X152 n4 recQs1835 tmp252)
    )
  )
)
(assert
  (forall ()
    (=> false false)
  )
)
(assert
  (forall ((n4 Int) (recQs1835 Int) (x169 Int))
    (=>
      (X152 x169 recQs1835 n4)
      (X83 x169 recQs1835)
    )
  )
)
(assert
  (forall ((n4 Int) (recQs1835 Int) (x169 Int) (x170 Int))
    (=>
      (and
        (X152 x169 recQs1835 n4)
        (X82 x170 x169 recQs1835)
      )
      (X153 x170 x169 recQs1835 n4)
    )
  )
)
(assert
  (forall ((n4 Int) (n47 Int) (recQs1835 Int) (tmp253 Int) (x166 Int) (x167 Int))
    (=>
      (and
        (= tmp253 1)
        (and
          (and
            (X152 n47 recQs1835 n4)
            (X81 x167 x166 recQs1835)
          )
          (>= x166 x167)
        )
      )
      (X136 tmp253 x167 x166 recQs1835 n4)
    )
  )
)
(assert
  (forall ((n4 Int) (n47 Int) (recQs1835 Int) (tmp254 Int) (x166 Int) (x167 Int))
    (=>
      (and
        (= tmp254 0)
        (and
          (and
            (X152 n47 recQs1835 n4)
            (X81 x167 x166 recQs1835)
          )
          (< x166 x167)
        )
      )
      (X136 tmp254 x167 x166 recQs1835 n4)
    )
  )
)
(assert
  (forall ((n4 Int) (n47 Int) (recQs1835 Int) (x166 Int) (x167 Int) (x168 Int))
    (=>
      (and
        (and
          (X152 n47 recQs1835 n4)
          (X81 x167 x166 recQs1835)
        )
        (X136 x168 x167 x166 recQs1835 n4)
      )
      (X80 x168 x167 x166 recQs1835)
    )
  )
)
(assert
  (forall ()
    (=> true X124)
  )
)
(check-sat)
(get-model)


; ; a solution of this CHC
; (model
;   (define-fun X83
;     ((v_0 Int) (v_1 Int)) Bool
;     (and
;       (>= (+ v_1 v_0) 1)
;       (>= (+ v_1 (* (- 1) v_0)) 1)
;     )
;   )
;   (define-fun X82
;     ((v_0 Int) (v_1 Int) (v_2 Int)) Bool
;     (and
;       (>= (+ v_1 v_2) 1)
;       (>= (+ (* (- 1) v_1) v_2) 1)
;     )
;   )
;   (define-fun X3
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int)) Bool
;     (and
;       (>= v_1 0)
;       (>= v_2 0)
;       (>= v_3 0)
;       (>= (+ v_6 (* (- 1) v_1)) 1)
;       (>= (+ v_5 (* (- 1) v_1) (* (- 1) v_2) (* (- 1) v_3)) 2)
;     )
;   )
;   (define-fun X4
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int)) Bool
;     (and
;       (>= v_0 0)
;       (>= v_1 0)
;       (>= v_2 0)
;       (>= (+ (* (- 1) v_0) v_5) 1)
;       (>= (+ (* (- 1) v_0) (* (- 1) v_1) (* (- 1) v_2) v_4) 2)
;     )
;   )
;   (define-fun X1
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int)) Bool true
;   )
;   (define-fun X6
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int)) Bool true
;   )
;   (define-fun X2
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int)) Bool
;     (and
;       (>= v_2 2)
;       (>= v_3 1)
;     )
;   )
;   (define-fun X170
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int)) Bool
;     (and
;       (>= v_2 0)
;       (>= v_3 0)
;       (>= (+ (* (- 1) v_1) v_6) 1)
;       (>= (+ (* (- 1) v_1) (* (- 1) v_2) (* (- 1) v_3) v_5) 2)
;       (>= v_1 1)
;     )
;   )
;   (define-fun X169
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) (v_7 Int)) Bool
;     (and
;       (>= v_3 0)
;       (>= v_4 0)
;       (>= (+ (* (- 1) v_2) v_7) 1)
;       (>= (+ (* (- 1) v_2) (* (- 1) v_3) (* (- 1) v_4) v_6) 2)
;       (>= v_2 1)
;     )
;   )
;   (define-fun X168
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) (v_7 Int) (v_8 Int) (v_9 Int) (v_10 Int) (v_11 Int) (v_12 Int)) Bool true
;   )
;   (define-fun X167
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) (v_7 Int) (v_8 Int) (v_9 Int) (v_10 Int) (v_11 Int)) Bool
;     (and
;       (>= v_1 1)
;       (>= v_2 0)
;       (>= (+ (* (- 1) v_0) v_11) 2)
;       (>= (+ (* (- 1) v_0) (* (- 1) v_1) (* (- 1) (- 1)) (* v_2 (- 1)) v_10) 3)
;       (>= v_0 0)
;     )
;   )
;   (define-fun X166
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) (v_7 Int)) Bool
;     (and
;       (>= v_2 1)
;       (>= v_3 0)
;       (>= v_4 0)
;       (>= (+ (* (- 1) v_2) v_7) 1)
;       (>= (+ (* (- 1) v_2) (* (- 1) v_3) (* (- 1) v_4) v_6) 2)
;     )
;   )
;   (define-fun X165
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) (v_7 Int) (v_8 Int) (v_9 Int) (v_10 Int) (v_11 Int) (v_12 Int)) Bool true
;   )
;   (define-fun X164
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) (v_7 Int) (v_8 Int) (v_9 Int) (v_10 Int) (v_11 Int)) Bool
;     (and
;       (>= v_0 0)
;       (>= v_1 0)
;       (>= v_2 1)
;       (>= (+ (* (- 1) v_0) v_11) 2)
;       (>= (+ (* (- 1) v_0) (* (- 1) v_1) (* (- 1) (+ (- 1) v_2)) v_10) 3)
;     )
;   )
;   (define-fun X163
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int)) Bool
;     (and
;       (<= v_0 0)
;       (>= v_0 0)
;       (>= v_1 0)
;       (>= v_2 0)
;       (>= (+ (* (- 1) v_0) v_5) 1)
;       (>= (+ (* (- 1) v_0) (* (- 1) v_1) (* v_2 (- 1)) v_4) 2)
;     )
;   )
;   (define-fun X162
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int)) Bool
;     (and
;       (>= v_2 0)
;       (>= v_6 1)
;       (<= (+ (* (- 1) v_5) v_2) (- 2))
;     )
;   )
;   (define-fun X161
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) (v_7 Int) (v_8 Int)) Bool true
;   )
;   (define-fun X160
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) (v_7 Int)) Bool
;     (and
;       (>= v_0 0)
;       (>= v_7 1)
;       (<= (+ (* (- 1) v_6) v_0) (- 2))
;     )
;   )
;   (define-fun X159
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) (v_7 Int)) Bool true
;   )
;   (define-fun X158
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int)) Bool
;     (and
;       (= (+ (* (- 1) v_0) v_3) 0)
;       (<= v_1 0)
;       (>= v_1 0)
;       (>= v_2 0)
;       (>= v_3 0)
;       (>= (+ (* (- 1) v_1) v_6) 1)
;       (>= (+ (* (- 1) v_1) (* (- 1) v_2) (* v_3 (- 1)) v_5) 2)
;     )
;   )
;   (define-fun X157
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int)) Bool
;     (and
;       (>= (+ v_0 (* (- 1) v_2)) 0)
;       (>= (+ v_3 (* (- 1) v_2)) 1)
;       (>= (+ v_0 (* (- 1) v_1)) 1)
;       (>= v_2 1)
;       (>= (+ v_1 v_0) 1)
;     )
;   )
;   (define-fun X156
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) (v_7 Int) (v_8 Int)) Bool true
;   )
;   (define-fun X155
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) (v_7 Int)) Bool
;     (and
;       (= v_1 0)
;       (= v_2 0)
;       (>= (+ v_4 (* (- 1) v_0)) 1)
;       (>= (+ v_7 (* (- 1) v_0)) 2)
;       (>= (+ v_4 (* (- 1) v_3)) 1)
;       (>= v_0 0)
;       (>= (+ v_3 v_4) 1)
;     )
;   )
;   (define-fun X154
;     ((v_0 Int) (v_1 Int)) Bool
;     (and
;       (>= (+ v_1 v_0) 1)
;       (>= (+ v_0 (* (- 1) v_1)) 1)
;     )
;   )
;   (define-fun X153
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int)) Bool true
;   )
;   (define-fun X152
;     ((v_0 Int) (v_1 Int) (v_2 Int)) Bool
;     (and
;       (= (+ (* (- 1) v_0) v_2) 0)
;       (>= (+ v_2 v_1) 1)
;       (>= (+ v_1 (* (- 1) v_2)) 1)
;     )
;   )
;   (define-fun X5
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int)) Bool
;     (and
;       (>= v_3 2)
;       (>= v_4 1)
;     )
;   )
;   (define-fun X126
;     ((v_0 Int) (v_1 Int)) Bool true
;   )
;   (define-fun X125
;     ((v_0 Int)) Bool true
;   )
;   (define-fun X124
;     () Bool true
;   )
;   (define-fun X94
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int)) Bool
;     (and
;       (>= v_2 1)
;       (>= (+ v_3 (* (- 1) v_2)) 1)
;     )
;   )
;   (define-fun X93
;     ((v_0 Int) (v_1 Int) (v_2 Int)) Bool
;     (and
;       (>= (+ v_2 (* (- 1) v_1)) 1)
;       (>= v_1 1)
;     )
;   )
;   (define-fun X86
;     ((v_0 Int) (v_1 Int) (v_2 Int)) Bool true
;   )
;   (define-fun X85
;     ((v_0 Int) (v_1 Int) (v_2 Int)) Bool
;     (>= v_2 2)
;   )
;   (define-fun X7
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int)) Bool true
;   )
;   (define-fun X81
;     ((v_0 Int) (v_1 Int) (v_2 Int)) Bool
;     (>= v_2 2)
;   )
;   (define-fun X80
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int)) Bool true
;   )
;   (define-fun X14
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int)) Bool
;     (and
;       (>= v_2 0)
;       (>= v_3 0)
;       (>= (+ (* (- 1) v_1) v_6) 1)
;       (>= (+ (* (- 1) v_1) (* (- 1) v_2) (* (- 1) v_3) v_5) 2)
;       (>= v_1 1)
;     )
;   )
;   (define-fun X136
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int)) Bool true
;   )
;   (define-fun X84
;     ((v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int)) Bool
;     (>= v_3 2)
;   )
; )