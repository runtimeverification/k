(set-option :auto-config false)
(set-option :smt.mbqi false)

; int extra
(define-fun int_max ((x Int) (y Int)) Int (ite (< x y) y x))
(define-fun int_min ((x Int) (y Int)) Int (ite (< x y) x y))
(define-fun int_abs ((x Int)) Int (ite (< x 0) (- 0 x) x))

; bool to int
(define-fun smt_bool2int ((b Bool)) Int (ite b 1 0))

(declare-fun expFunc (Int Int) Int)

(assert (forall ((x1 Int) (y1 Int) (x2 Int) (y2 Int))
  (=> (and (<= x1 x2) (<= y1 y2))
    (<= (expFunc x1 y1) (expFunc x2 y2))
  )
))

