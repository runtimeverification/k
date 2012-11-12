// testing two tuple arguments to a function

let f {a,b} {x,y} = a{x,y} + b{x,y}
in f {fun {x,y} -> x * y, fun {x,y} -> x + y} {10,20}
