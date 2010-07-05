kmod THREADS-PROGRAMS is including THREADS + IMP + REF + IO + LAMBDA + HALT + IDS
  op p17 : -> K
  macro p17 = ((lambda x . lambda y . (
           (spawn(*x:=0));
           ((while(1<=*x) do (*y:=*y+1)) ;
           print(*y))
           )) (ref 1)) (ref 0)
        
  op p18 : -> K
  macro p18 =  (lambda x . ( 
                (spawn ((rendezvous 1) ; (print(*x)) ; (rendezvous 2))) ;
                (spawn ((rendezvous 3) ; (print(*x)) ; (rendezvous 4))) ;
                (print(*x)) ;
                (*x := *x + 1) ;
                (rendezvous 1) ;  (rendezvous 2) ;
                (*x := *x + 1) ;
                (rendezvous 3) ; (rendezvous 4))) (ref 1)
   

  op p19 : -> K
  macro p19 = (lambda x . ( 
                (spawn ((*x:= *x + 1) ; (rendezvous 1) ));
                (*x := *x + 1) ;
                (rendezvous 1) ;
                (print(*x)))) (ref 1)
    
  op p20 : -> K
  macro p20 = (lambda x . ( 
                (spawn ((acquire(x)) ; (*x:= *x + 1) ; (release(x)) ; (rendezvous 1) ));
                (acquire(x)) ;
                (*x := *x + 1) ;
                (release(x)) ;
                (rendezvous 1) ;
                (print(*x)))) (ref 1)
    
  op p21 : -> K
  macro p21 = (lambda x . ( 
                (spawn ((acquire(x)) ; (rendezvous 1) ; (*x:= *x + 1) ; (halt(0)) ));
                (rendezvous 1) ;
                (acquire(x)) ;
                (*x := *x + 1) ;
                (release(x)) ;
                (print(*x)))) (ref 1)
endkm
