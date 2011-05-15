kmod IO-PROGRAMS is including IO + MU + LAMBDA + IF + EXP + IDS
  op p14 : -> K
  macro p14 = print(read)

  op p15 : -> K 
  macro p15 = print((mu f . (lambda x . (print(x) ; if x * x <= 0 then 1 else ((f read) * x)))) read)
endkm
