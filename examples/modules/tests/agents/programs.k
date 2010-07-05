kmod AGENTS-PROGRAMS is including AGENTS + THREADS + IO + LAMBDA + IDS
  op p22 : -> K
  macro p22 = ((lambda y . lambda z . (send z to y))
          (newAgent(((lambda y . (sendSynch me to y)) (receiveFrom parent)) ; 
                    (spawn haltAgent) ; (print(receive))))) 
           (newAgent(((lambda z . ((send 17 to z) ; (print(z)))) receive)))
endkm
