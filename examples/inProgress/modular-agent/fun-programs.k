kmod FUN-PROGRAMS is including FUN + EXP + IDS
  op p2 : -> K
  macro p2 = lambda x . x

  op p3 : -> K 
  macro p3 = x mu f . lambda x . (f x)

  op p4 : -> K
  macro p4 = a ((lambda z . (z z)) lambda x.lambda y.(x y))

  op p5 : -> K
  macro p5 = a ((lambda x.lambda y.(x y)) y)

  op p6 : -> K
  macro p6 = ((lambda x . x + 7) 10)
  
  op p7 : -> K
  macro p7 = ((lambda x . if 5 <= 3 then x + 7 else 0) y)

  op p8 : -> K 
  macro p8 = ((mu f . (lambda x . if x <= 0 then 1 else ((f (x + -1)) * x))) 5)
endkm
