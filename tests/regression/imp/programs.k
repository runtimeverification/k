kmod IMP-PROGRAMS is  including WHILE + REF + LAMBDA + EXP + IDS
  op p16 : -> K 
  macro p16 = ((lambda x.(lambda y.((while(2<=*y) do (
          (*x:= _*_(*x,*y));
          (*y:=(*y+-1))
       )); *x))) (ref 1)) (ref 5) 
endkm
