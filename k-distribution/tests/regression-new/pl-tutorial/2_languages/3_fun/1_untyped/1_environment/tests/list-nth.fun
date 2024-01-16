letrec nth = fun 1 [h|t] -> h
               | n [h|t] -> nth (n - 1) t
in nth 4 [5,4,3,2,1]
