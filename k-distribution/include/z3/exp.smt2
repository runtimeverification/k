(declare-fun exp (Int Int) Int)

(assert (forall ((x1 Int) (y1 Int) (x2 Int) (y2 Int))
  (=> (and (<= x1 x2) (<= y1 y2))
    (<= (exp x1 y1) (exp x2 y2))
  )
))
