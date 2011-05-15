kmod MU-PROGRAMS is including MU + LAMBDA + IF + EXP + IDS
  op p7 : -> K 
  macro p7 = x mu f . lambda x . (f x)

  op p8 : -> K 
  macro p8 = ((mu f . (lambda x . if x <= 0 then 1 else ((f (x + -1)) * x))) 5)
endkm
