letrec fibo n x y = if n==0
                    then x
                    else let* x=x+y
                         and  y=x-y
                          in  fibo (n-1) x y
in fibo 7 1 1
