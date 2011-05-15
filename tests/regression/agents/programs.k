kmod AGENTS-PROGRAMS is including AGENTS + THREADS + WHILE + IO + REF + LAMBDA + EXP + IDS
  op p22 : -> K
  macro p22 = ((lambda y . lambda z . (send z to y))
          (newAgent(((lambda y . (sendSynch me to y)) (receiveFrom parent)) ; 
                    (spawn haltAgent) ; (print(receive))))) 
           (newAgent(((lambda z . ((send 17 to z) ; (print(z)))) receive)))
           
  op p23 : -> K
  macro p23 = (lambda x .  (
  (while (*x <= 3) do (
    (newAgent (
      (print me);
      barrier)) ;
    (*x := *x + 1)
  )) ; 
  barrier;
  (print me))) (ref 1)

  op p24 : -> K
  macro p24 = (lambda x .  (
  (while (*x <= 3) do (
    (newAgent (print receive)) ;
    (*x := *x + 1)
  )) ; 
  broadcast 0)) (ref 1)
endkm
