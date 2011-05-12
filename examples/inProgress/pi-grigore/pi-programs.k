kmod PI-PROGRAMS is including PI-SYNTAX
  ops x y z v : -> Id 
  op p1 : -> Proc
  macro p1 = new x . (send z on x . () || receive y on x . send x on y . receive y on x . ()) || receive v on z . send v on v . ()
endkm
