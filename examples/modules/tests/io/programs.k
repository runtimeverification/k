kmod IO-PROGRAMS is including IO + MU + EXP + IDS
  op p14 : -> K
  macro p14 = print(read)

  op p15 : -> K 
  macro p15 = print((mu f . (lambda x . if print(x) * x <= 0 then 1 else ((f read) * x))) read)
endkm