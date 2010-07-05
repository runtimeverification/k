kmod CALLCC-PROGRAMS is including CALLCC + LAMBDA + EXP + IDS
  ops k return : -> Id 

  op p10 : -> K 
  macro p10 = callcc (lambda k . 7)

  op p11 : -> K 
  macro p11 = callcc (lambda k . (k 7))

  op p12 : -> K 
  macro p12 = callcc (lambda k . ((k 7) + 5))

--- using callcc for returning
  op p13 : -> K 
  macro p13 = ((lambda f . (callcc (f -5)))( lambda x . (lambda return . ((lambda x . (0 / 0)) (
          if (0 <= x)
          then (return 0)
          else (return 1)
        ))))) + 3
---
endkm
