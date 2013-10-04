// testing tuple arguments to a function

let f = fun {} {a,b} q {} {x,y} {} -> a{x,y} + b{x,y}
in f {} {fun {x,y} -> x * y, fun {x,y} -> x + y} 3 {} {10,20} {}
