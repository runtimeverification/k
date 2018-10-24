(declare-sort Key)
(declare-sort Val)
(define-sort MyMap () (Array Key Val))

(declare-fun h (Int) Int)
(assert (= (h 0) (h 1)))
