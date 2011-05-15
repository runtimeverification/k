kmod LAMBDA-PROGRAMS is including LAMBDA + IF + EXP + IDS
  op p2 : -> K
  macro p2 = lambda x . x

  op p3 : -> K
  macro p3 = a ((lambda z . (z z)) lambda x.lambda y.(x y))

  op p4 : -> K
  macro p4 = a ((lambda x.lambda y.(x y)) y)

  op p5 : -> K
  macro p5 = ((lambda x . x + 7) 10)
  
  op p6 : -> K
  macro p6 = ((lambda x . if 5 <= 3 then x + 7 else 0) y)
endkm
