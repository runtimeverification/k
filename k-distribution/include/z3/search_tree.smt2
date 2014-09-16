(set-option :smt.mbqi.max_iterations 10)

; int extra
(define-fun int_max ((x Int) (y Int)) Int (ite (< x y) y x))
(define-fun int_min ((x Int) (y Int)) Int (ite (< x y) x y))
(define-fun int_abs ((x Int)) Int (ite (< x 0) (- 0 x) x))

; bool to int
(define-fun smt_bool2int ((b Bool)) Int (ite b 1 0))

; sets as arrays
(define-sort IntSet () (Array Int Bool))
(define-fun smt_set_mem ((x Int) (s IntSet)) Bool (select s x))
(define-fun smt_set_add ((s IntSet) (x Int)) IntSet  (store s x true))
(define-fun smt_set_emp () IntSet ((as const IntSet) false))
(define-fun smt_set_cup ((s1 IntSet) (s2 IntSet)) IntSet ((_ map or) s1 s2))
(define-fun smt_set_cap ((s1 IntSet) (s2 IntSet)) IntSet ((_ map and) s1 s2))
(define-fun smt_set_com ((s IntSet)) IntSet ((_ map not) s))
(define-fun smt_set_ele ((x Int)) IntSet (smt_set_add smt_set_emp x))
(define-fun smt_set_dif ((s1 IntSet) (s2 IntSet)) IntSet (smt_set_cap s1 (smt_set_com s2)))
(define-fun smt_set_sub ((s1 IntSet) (s2 IntSet)) Bool (= smt_set_emp (smt_set_dif s1 s2)))
(define-fun smt_set_lt  ((s1 IntSet) (s2 IntSet)) Bool (forall ((__mbqi__i Int) (__mbqi__j Int)) (implies (>= __mbqi__i __mbqi__j) (not (and (select s1 __mbqi__i) (select s2 __mbqi__j))))))
(define-fun smt_set_le  ((s1 IntSet) (s2 IntSet)) Bool (forall ((__mbqi__i Int) (__mbqi__j Int)) (implies (>  __mbqi__i __mbqi__j) (not (and (select s1 __mbqi__i) (select s2 __mbqi__j))))))

; sequence axioms
(declare-sort IntSeq)

(declare-fun smt_seq_concat (IntSeq IntSeq) IntSeq)
(declare-fun smt_seq_elem (Int) IntSeq)
(declare-fun smt_seq_nil () IntSeq)

(declare-fun smt_seq2set (IntSeq) IntSet)
(declare-fun smt_seq_sorted (IntSeq) Bool)

