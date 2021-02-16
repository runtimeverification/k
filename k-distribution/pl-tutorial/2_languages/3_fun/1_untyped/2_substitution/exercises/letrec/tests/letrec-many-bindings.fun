letrec f1   = fun 0 -> 1 | n -> n * f2 (n - 1)
and    f2 n = f3 n
and    f3 n = f4 n
and    f4 n = f5 n
and    f5 n = f6 n
and    f6 n = f7 n
and    f7 n = f1 n
in (f1 5)
