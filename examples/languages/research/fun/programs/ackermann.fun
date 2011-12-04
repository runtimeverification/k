letrec ackermann(m,n) =
         if m == 0 then n + 1 else
         if n == 0 then ackermann(m - 1, 1) else
         ackermann(m - 1, ackermann(m, n - 1))
in ackermann(2,3)
