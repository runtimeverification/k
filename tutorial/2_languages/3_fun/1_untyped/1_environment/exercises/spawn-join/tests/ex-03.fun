let x = read
in  let t1 = spawn &x := x / 2
    in let t2 = spawn &x := x + 10
       in (join t1; join t2; print x)
