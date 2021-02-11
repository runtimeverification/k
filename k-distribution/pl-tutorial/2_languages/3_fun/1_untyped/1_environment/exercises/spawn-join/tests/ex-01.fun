let x = 1
in (spawn (&x := x + 1; print x); &x := x + 1; print x)
