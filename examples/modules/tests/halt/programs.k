kmod HALT-PROGRAMS is including HALT + MU + LAMBDA + IF + EXP + IDS
  op p9 : -> K 
  macro p9 = ((mu f . (lambda x . lambda y . if x <= 0 then halt(y) else ((f (x + -1)) (y * x)))) 5) 1
endkm
