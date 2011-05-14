kmod QUOTE-UNQUOTE-PROGRAMS is including QUOTE-UNQUOTE + IO + WHILE + REF + MU + LAMBDA + EXP + IDS
  op p25 : -> K
  macro p25 = 
   ((((lambda n . lambda c . lambda i . lambda x .
   ((while (*i <= n) do (
     (*c := quote(unquote(*c) + x)) ;
     (*i := *i + 1)
   )) ;
   print(eval(*c)))) 5) (ref (quote 1))) (ref 1)) 10
   
  op p26 : -> K
  macro p26 = (lambda c . ((lambda b . print(eval(b))) (quote(quote(unquote(unquote(lift c))))))) 10
 

  op p27 : -> K
  macro p27 = 
   (((lambda n . lambda c . lambda i .
   (while (*i <= n) do (
     (*c := quote(quote(unquote(unquote(*c)))));
     (*i := *i + 1)
   ) ;
   print(eval(*c)))) 5) (ref (quote 1))) (ref 1)


  op p28 : -> K
  macro p28 = 
   (lambda x . 
   print(eval(quote(1 + 2 + unquote(x) + 4 + 5)))) (quote 2) 

  ops genpow cube : -> Id

  op p29 : -> K
  macro p29 = 
   (lambda cube . ((print (cube 5)) ; (print (cube 10))))
   (lambda x . (eval ((mu genpow . (lambda n . (
              if (n <= 0)
              then (quote 1)
              else (quote (_*_(x,(unquote (genpow (n + -1))))))
            ))) 3))
   )
endkm
