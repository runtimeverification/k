// letrec f x = if x<=0 then 1 else x * f(x - 1)
// in f (f 4)

letrec f = fun 0 -> 1
           |   x -> x * f(x - 1)
in f (f 4)

// 620448401733239439360000
