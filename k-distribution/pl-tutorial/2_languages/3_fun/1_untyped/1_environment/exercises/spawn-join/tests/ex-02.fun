let x = 1
in (join spawn (&x := x + 1; print x); &x := x + 1; print x)
