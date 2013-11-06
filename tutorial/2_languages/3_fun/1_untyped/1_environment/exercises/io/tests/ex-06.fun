letrec all n = if n<0 then 0 else (print n; print "\n"; all(n-1))
in all 10
